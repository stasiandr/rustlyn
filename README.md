# Rustlyn

A static analyzer for C#, written in Rust, that happens to be a compiler as well. It
follows the architecture of [Roslyn](https://github.com/dotnet/roslyn).

Rustlyn answers questions about a whole C# project: what a change reaches, whether it
leads to a given SDK, where a value comes from, how a method can fail and under which
conditions, which field two threads touch with no lock between them. An analysis is
worth what its reading of the code is worth, so Rustlyn reads C# the way the compiler
does, and to keep that honest it is one. It compiles Roslyn itself, and the
`Roslyn.dll` it builds compiles Rustlyn's build of Roslyn again, identical byte for
byte. It compiles a 45,000-file production Unity project the way Unity does, with no
false errors. The same engine serves an editor, a decompiler and hot reload into a
running Unity editor.

## What it does

### The analyzer

* **Whole-project analyses.** `rustlyn-analyzer` computes the blast radius of a change,
  says whether a change leads to a given SDK through calls, fields and ECS components,
  traces where a value comes from, and explains how a method can fail and under which
  conditions. It also reads Unity assets and their references, and NuGet packages. Its
  command-line tools are `rustlyn-blast` (also an MCP server for coding agents),
  `rustlyn-reach`, `rustlyn-graph` and `rustlyn-fail`. See [docs/analyzer.md](docs/analyzer.md).
* **Diagnostics.** The compiler's own errors and warnings, the IDE analyzers
  (IDE0001–IDE0090, IDE1006) with severities from `.editorconfig`, and analyses Roslyn
  does not have: thread safety (a field two threads touch with no lock, Unity's
  main-thread API reached from a background thread) and failability. An error is
  reported only where it is certain: on real code a false one costs more than a missed
  one.
* **Editor services.** `rustlyn-ide` arranges the analysis in cached layers for an
  editor: colouring, outline, project index, go to definition, references, completion,
  rename, code actions, formatting and more. It loads `.sln`/`.csproj` and Unity
  projects, and `rustlyn-ffi` exposes it through a C ABI.
* **Reading assemblies.** A metadata reader, an IL disassembler and a decompiler
  (`rustlyn-decompile`). The decompiler turns assemblies back into readable C#,
  reconstructing lambdas, iterators and `async` state machines.

### The compiler underneath

* **Parsing.** A full-fidelity lexer, preprocessor and parser for the whole language
  through C# 14/15. On all 18,224 source files of Roslyn, the tree reproduces the source
  byte for byte.
* **Binding.** Symbols, declarations, overload resolution, type inference and
  conversions against real reference assemblies. The 2,242 files of the Roslyn compiler
  bind with zero diagnostics against .NET 11.
* **Emitting.** Real PE/ECMA-335 assemblies that run on .NET, written the way `csc`
  writes them: generics, lambdas and closures, iterators, `async`/`await`, pattern
  matching, records, unsafe code, expression trees and more. 99.99% of the 61,228 method
  bodies in the Roslyn corpus compile to IL.
* **Self-hosting Roslyn.** A `Roslyn.dll` built by Rustlyn compiles and runs programs and
  compiles Roslyn again. The second and third generations are byte-for-byte identical.
* **Speed.** On Roslyn's own sources, a batch build is about 1.7 times faster than a warm
  `csc` compiler server. The output is deterministic for any thread count.
* **Unity.** Rustlyn compiles a Unity project the way Unity last built it. On a large
  production project (45,510 files, packages included) it reports no false errors, gives
  5,198 of the 5,505 warnings Unity's own compile reports, and adds none of its own.
* **Hot reload.** An edited method runs in a live Unity editor 1.4 s after you save,
  with no domain reload. The same edit through Unity's own compile takes 53 s.

The APIs are pre-1.0 and may still change. Behaviour that knowingly differs from Roslyn
is listed in [docs/differences-from-roslyn.md](docs/differences-from-roslyn.md), and
what comes next in [docs/roadmap.md](docs/roadmap.md).

## Quick start

You need the Rust toolchain (the version is pinned in `rust-toolchain.toml`; `rustup`
picks it up automatically). To run what Rustlyn compiles, you need a .NET runtime;
to compile against the real framework, a .NET SDK or shared framework directory.

```sh
git clone https://github.com/stasiandr/rustlyn
cd rustlyn
cargo build --release
```

Ask what a change reaches, and how a method can fail:

```sh
cargo build --release -p rustlyn-analyzer
target/release/rustlyn-blast <project root>                  # the working copy against HEAD, with risks
target/release/rustlyn-fail <project root> Player.cs:42      # how the member at that line can fail
target/release/rustlyn-graph <project root> Player.cs:42:17  # where the value there comes from
```

Compile a C# file to an assembly and run it:

```sh
cargo run --release -p rustlyn-emit --example build -- Program.cs out/
dotnet out/Program.dll

# csc-style options: more sources, language version, entry point, checked, defines
cargo run --release -p rustlyn-emit --example build -- Program.cs out/ --source Other.cs \
    --langversion 9 --main N.Program --checked --define TRACE
```

Look at what the compiler sees:

```sh
cargo run -p rustlyn-syntax --example dump -- Program.cs         # parse tree
cargo run -p rustlyn-semantics --example symbols -- Program.cs   # declaration table
cargo run -p rustlyn-semantics --example typeof -- Program.cs    # type of every expression
cargo run -p rustlyn-semantics --example bound -- Program.cs     # bound tree
cargo run -p rustlyn-interpret --example run -- Program.cs       # interpret the program
```

Read assemblies:

```sh
cargo run -p rustlyn-metadata --example dump -- out/Program.dll    # metadata tables
cargo run -p rustlyn-metadata --example disasm -- out/Program.dll  # IL
cargo run -p rustlyn-decompile -- out/Program.dll [Type[::Method]] [--references <framework dir>]
```

Ask a project what an editor would ask, with timings:

```sh
find src -name '*.cs' | cargo run --release -p rustlyn-ide --example semantic -- <project root>
```

As a library:

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

More entry points are listed in [docs/development.md](docs/development.md#examples).

## Crates

| Crate | Description |
|---|---|
| [`rustlyn-text`](crates/rustlyn-text) | Source text, spans and line mapping |
| [`rustlyn-diagnostics`](crates/rustlyn-diagnostics) | Diagnostics and C# error codes |
| [`rustlyn-syntax`](crates/rustlyn-syntax) | Lexer and syntax tree (green/red), parser |
| [`rustlyn-semantics`](crates/rustlyn-semantics) | Symbols, declarations and semantic analysis (binder, `Compilation`) |
| [`rustlyn-interpret`](crates/rustlyn-interpret) | A tree-walking interpreter for the subset of C# Rustlyn understands |
| [`rustlyn-emit`](crates/rustlyn-emit) | IL and ECMA-335 metadata emission |
| [`rustlyn-metadata`](crates/rustlyn-metadata) | Reading ECMA-335 metadata out of a .NET assembly |
| [`rustlyn-decompile`](crates/rustlyn-decompile) | Turning a .NET assembly back into readable C# |
| [`rustlyn-ide`](crates/rustlyn-ide) | The editor-facing side: open, colour, outline, index and decompile, each layer cached |
| [`rustlyn-analyzer`](crates/rustlyn-analyzer) | Whole-project analyses: blast radius, value graph, failability, Unity assets, NuGet |
| [`rustlyn-ffi`](crates/rustlyn-ffi) | The C ABI over `rustlyn-ide`, for an editor not written in Rust |

## Documentation

* [docs/analyzer.md](docs/analyzer.md): the whole-project analyses and their command-line tools
* [docs/status.md](docs/status.md): what works, in detail, and how it is validated
* [docs/architecture.md](docs/architecture.md): the pipeline and design decisions
* [docs/performance.md](docs/performance.md): benchmark against `csc`
* [docs/editor.md](docs/editor.md): editor services and the C ABI
* [docs/differences-from-roslyn.md](docs/differences-from-roslyn.md): known differences
* [docs/roadmap.md](docs/roadmap.md): what's next and past milestones
* [docs/development.md](docs/development.md): building, testing and the `tools/` harnesses

## Development

```sh
cargo test --no-fail-fast
crates/rustlyn-ffi/tests/run.sh   # the C header against the real library
cargo clippy --all-targets
cargo fmt --all
```

Tests that emit assemblies also run them when a `dotnet` host is available; see
[docs/development.md](docs/development.md) for the environment variables and the
benchmark harnesses in `tools/`.

## License

MIT © 2026 Stanislav Datsyuk. See [LICENSE](LICENSE).
