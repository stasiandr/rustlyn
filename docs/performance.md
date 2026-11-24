# Performance

There is something to compare against: the same input can be given to the real `csc`.
[`tools/bench/run.py`](../tools/bench/run.py) runs both on the same list of files, with
the same `/r:` set from one framework directory, the same `/define:` symbols, and
`/optimize- /debug- /deterministic+`. What is and is not measured is described in
[`tools/bench/README.md`](../tools/bench/README.md).

## Batch compilation

| corpus | files | lines | csc | csc+server | rustlyn | csc CPU | rustlyn CPU | csc RSS | rustlyn RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| hello | 1 | 6 | 0.82 s | 0.17 s | 0.24 s | 0.8 s | 0.4 s | 157 MiB | 171 MiB |
| dependencies | 146 | 26 273 | 2.22 s | 0.97 s | 0.45 s | 4.9 s | 0.9 s | 254 MiB | 184 MiB |
| core | 1075 | 236 597 | 8.57 s | 3.28 s | 1.99 s | 23.8 s | 4.7 s | 511 MiB | 397 MiB |
| everything | 2243 | 790 358 | 30.68 s | 10.67 s | 6.13 s | 96.6 s | 16.2 s | 1130 MiB | 1038 MiB |

Best of three runs; 4 cores of a 2.80 GHz Xeon, csc 5.9.0 (SDK 10.0.401) against
.NET 10.0.12. Output: 10.64 MB from csc, 10.69 MB from rustlyn. The corpora are
Roslyn's own sources (see the bench README for what each contains).

There are two csc columns, and the second matters more. **`csc`** is the compiler run
as a plain process. **`csc+server`** is the same with `/shared`, the way MSBuild always
invokes it: the work goes to a `VBCSCompiler` process that outlives the build and keeps
a warm JIT and parsed reference assemblies. The difference between the columns is the
cost of a compiler written in .NET re-reading some 150 framework assemblies every time;
on the full corpus it is almost threefold.

The fair comparison is against the second column: **on the full corpus rustlyn is
1.7 times faster than a warm csc** (6.13 s vs 10.67 s), 1.6 times on `core`, and twice
as fast on `dependencies`. Before parallelization the same machine took 36.1 s on the
full corpus, 9.3 s on `core` and 1.55 s on `dependencies`: rustlyn was single-threaded
and 3.4 times slower than the server.

Comparing with the first column is worthless ("csc was measured in a configuration it
never runs in"). Rustlyn also does less work at the time of this measurement: csc runs
nullable analysis, full definite assignment and reachability analysis, writes all
attributes and the full set of diagnostics, while rustlyn replaced 10 bodies with stubs
on the full corpus.

## Where the time goes

`RUSTLYN_TIMINGS=1` prints the phases; `RUSTLYN_THREADS=1` puts everything on one core
and produces the same bytes.

* **Parsing and declarations: 0.9 s.** Files are parsed on all cores but one, and that
  one declares them in order as they become ready (and parses the next one itself when
  it is not ready yet): declarations go file by file, and the first files are parsed
  long before the last. Nodes that declarations look for inside bodies (local functions,
  `new { … }`, the `field` name) are collected by the pass that follows parsing, not by
  walking every body.
* **Reference assemblies: 0.16 s.** Reference symbols are numbered after source
  symbols, so loading waits for declarations; but each assembly's members are read in
  parallel into a separate table with temporary numbers and then appended in assembly
  order, so the numbers are the same as when reading assemblies one after another.
* **Binding bodies and the emit plan: 2.9 s.** Once declarations are done, bodies do
  not depend on each other: whatever binding one body learns and caches (base types,
  constants, conversions) is a property of the compilation that any other would learn
  the same way. Threads bind bodies in the order the plan will ask for them, and the plan
  follows and waits only where it has caught up, plus once for all of them before naming
  synthesized delegate types. The hottest questions (`System.Object` in every
  inheritance walk, base types, symbol types) are answered without locks, one slot per
  symbol.
* **IL generation and metadata writing: 2.1 s, one core.** Token order is determined by
  generation order, and parallelizing it while keeping the bytes would need a two-pass
  scheme with symbolic tokens.

The output does not change: the assembly is byte-for-byte the same for any thread count
and from run to run. (Two places where order depended on a hash were fixed along the
way: captured parameters in a display class, and shared-read flags in pattern
matching.) All assemblies of the `CompileAndVerify` benchmark match the ones built
single-threaded.

## Memory

Rustlyn uses less memory than csc even though the bound bodies of the whole corpus live
until they are emitted. Green tokens with no value of their own (punctuation, keywords,
names) and small nodes over them (`x` as a name, `int` as a type) with identical trivia
share one allocation for every place they are written, as Roslyn's `SyntaxNodeCache`
does; that is a third of the peak. The backend also stores bodies without what only an
editor needs (what each name means, diagnostics).

## Startup

`hello` is a separate case: one file, 0.17 s for the warm server against 0.24 s for
rustlyn. Nothing is computed there; it is pure startup cost, and 0.16 s of it is the
symbols of about 150 framework assemblies, which are loaded whole rather than on demand
as Roslyn does. The server does not do this at all.

## Why the disk cache is not used for batch builds

The disk cache from `rustlyn-ide` is not wired into batch builds. A snapshot of the full
corpus compilation (58 MB) reads in 0.43 s against 1.5 s for parsing, declarations and
references, but it does not store trees, and binding needs all of them, so parsing
(2.7 s of CPU time) would have to happen anyway. The gain would be at most 0.3 s on an
unchanged corpus and zero on a changed one.

## Editor numbers

Latency figures for the editor layers (colouring, project index, go to definition, find
references, completion) are in [editor.md](editor.md).
