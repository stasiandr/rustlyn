# Development

## Building and testing

```sh
cargo build --release
cargo test --no-fail-fast
crates/rustlyn-ffi/tests/run.sh   # the C header against the real library
cargo clippy --all-targets
cargo fmt --all
```

The Rust version is pinned in [`rust-toolchain.toml`](../rust-toolchain.toml): every
stable release brings new clippy lints, and CI builds with `-D warnings`. Bump it in a
separate commit, together with whatever the new clippy finds.

For iterating on the compiler there is a `fast` profile (see the workspace
[`Cargo.toml`](../Cargo.toml)): optimized enough to run the benchmarks, built several
times faster than `release`. `cargo build --profile fast -p rustlyn-emit --example build`
puts the compiler at `target/fast/examples/build`.

## Tests that need .NET

The `rustlyn-emit` tests run what they build. If `dotnet` is not found they still build
the assembly and note that they could not run it; point at a host explicitly with
`RUSTLYN_DOTNET=/path/to/dotnet cargo test`. `RUSTLYN_REQUIRE_DOTNET=1` makes a missing
host an error rather than a note; CI runs the tests that way, with .NET 8 (requested by
the programs in `programs.rs`) and .NET 10.

`RUSTLYN_ROUNDTRIP=1` also runs every program in `against_references.rs` through the
decompiler: the C# read back is compiled again and must print the same thing. Programs
that cannot do this yet are listed in
[`crates/rustlyn-emit/tests/roundtrip_known.txt`](../crates/rustlyn-emit/tests/roundtrip_known.txt);
with `RUSTLYN_ROUNDTRIP=all` they are tried too, and fixed ones report
`ROUNDTRIP-FIXED` so they can be removed from the list.

`RUSTLYN_FRAMEWORK` names a shared framework directory for the tests (and the
decompiler) that read real assemblies.

## Fuzzing

The editor layer's fuzzer ([`crates/rustlyn-ide/examples/fuzz.rs`](../crates/rustlyn-ide/examples/fuzz.rs))
runs nightly ([`.github/workflows/fuzz.yml`](../.github/workflows/fuzz.yml)):

```sh
cargo run --release -p rustlyn-ide --example fuzz -- \
    --corpus <dir> [--corpus <dir>…] --out <dir> [--jobs 4] [--minutes 30] [--semantic]
cargo run --release -p rustlyn-ide --example fuzz -- --replay <out>/findings/<id>
```

## Useful environment variables

| Variable | Effect |
|---|---|
| `RUSTLYN_TIMINGS=1` | print time per compilation phase |
| `RUSTLYN_THREADS=1` | run on one core (output bytes are the same) |
| `RUSTLYN_DOTNET` | the `dotnet` host tests run programs with |
| `RUSTLYN_REQUIRE_DOTNET=1` | fail instead of skipping when no host is found |
| `RUSTLYN_ROUNDTRIP=1` / `all` | round-trip emitted programs through the decompiler |
| `RUSTLYN_FRAMEWORK` | shared framework directory for the decompiler and reference tests |

## Harnesses in `tools/`

Each measures the compiler against something it did not write. They expect inputs
(Roslyn checkout, .NET SDKs, library sources) under a configurable root; see each
README.

| Directory | What it measures |
|---|---|
| [`tools/bench`](../tools/bench/README.md) | batch compile time, CPU and memory against `csc`, on Roslyn's own sources ([results](performance.md)) |
| [`tools/cav`](../tools/cav/README.md) | Roslyn's `CompileAndVerify` tests as programs with expected output, built by Rustlyn and run on .NET |
| [`tools/diag`](../tools/diag/README.md) | Roslyn's `VerifyDiagnostics` tests: does Rustlyn reject wrong programs with the right errors |
| [`tools/oss`](../tools/oss/README.md) | open-source libraries compiled from source, then used from small programs |
| [`tools/selfhost`](../tools/selfhost) | the driver that makes the Roslyn built by Rustlyn compile Roslyn again |
| [`tools/unity`](../tools/unity) | hot reload into a running Unity editor, and its fuzzing |

## Examples

Most entry points are examples rather than binaries. The main ones:

| Crate | Examples |
|---|---|
| `rustlyn-syntax` | `dump` (parse tree), `fidelity` (round-trip a corpus), `diverge`, `shapes` |
| `rustlyn-semantics` | `symbols`, `typecheck`, `typeof`, `bound`, `bind` (corpus sweep), `untyped`, `diagnose`, `load`, `resx`, `constraints`, `redeclare` |
| `rustlyn-interpret` | `run` |
| `rustlyn-emit` | `build` (the compiler driver), `assemble` (one assembly from a corpus), `coverage`, `incremental`, `serve`, `mutate` |
| `rustlyn-metadata` | `dump`, `disasm`, `inspect`, `sweep`, `verify` |
| `rustlyn-ide` | `semantic`, `save`, `fuzz`, `hot`, `stubs`, plus analysis examples |
| `rustlyn-decompile` | the `decompile` binary (`cargo run -p rustlyn-decompile -- <assembly.dll>`) |

Each example's source starts with a comment explaining its arguments.
