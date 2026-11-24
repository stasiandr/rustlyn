# Benchmark: csc vs rustlyn

`run.py` compiles the same set of sources with two compilers (the real `csc` from the
.NET SDK and rustlyn's `assemble`) and measures wall time, CPU time, peak memory and the
size of the output assembly.

```
python3 tools/bench/run.py --dotnet /path/to/dotnet --roslyn /path/to/roslyn --repeat 3
```

The corpus is Roslyn's own sources:

| name | contents |
| --- | --- |
| `hello` | one file printing a line |
| `dependencies` | `src/Dependencies` |
| `core` | `dependencies` + `src/Compilers/Core/Portable` and `Core/AnalyzerDriver` |
| `everything` | `core` + `src/Compilers/CSharp/Portable` and `CSharp/CSharpAnalyzerDriver` |

Results are in [docs/performance.md](../../docs/performance.md).

## How it is measured

Each run happens in a separate wrapper process which, after the child exits, takes
`resource.getrusage(RUSAGE_CHILDREN)`; otherwise `ru_maxrss` would accumulate across
runs. The best of `--repeat` runs is taken. The first run of each compiler warms the
file cache.

Both compilers get exactly the same input:

* the same list of files (`--recurse` is not used; the list is built up front and given
  to csc through an rsp file and to rustlyn on stdin);
* the same set of `/r:`: every DLL in the chosen framework directory;
* the same `/define:` (`NET`, `NETCOREAPP`, `NET11_0`, the whole `NETx_0_OR_GREATER`
  ladder and so on);
* `/optimize- /debug- /deterministic+`.

`tools/bench/generated/AnalyzerConfig.RegexGenerator.g.cs` is the output of the
`[GeneratedRegex]` generator, written out by hand: neither compiler runs source
generators, and without this file `csc` fails with CS8795. Both get the file.

The two resource classes (`CodeAnalysisResources`, `CSharpResources`) are generated from
`.resx` by the `resx` example before the benchmark runs and sit in the corpus as ordinary
sources, again the same for both.

## The compiler server

By default `csc` runs bare here, without `/shared`. That is an honestly cold case on
both sides, but not the one csc works in during a real build: MSBuild always passes
`/shared`, and then the work goes to a `VBCSCompiler` process that outlives the build and
keeps a warm JIT and `MetadataAndSymbolCache`, an LRU of 500 parsed reference
assemblies. The `--shared` flag adds a third column with that mode.

Only wall time is measured there. The work happens in a foreign process that is not a
descendant of the measured one, so CPU time and peak memory do not apply.

Before measuring, `--repeat` warm-up runs are made and discarded: the first calls through
a fresh server run at tier 0, and on `core` that is a threefold difference (6.6 s vs
2.5 s).

The server has to be able to launch a host for itself. In a container `dotnet` is
usually not on PATH in a way it can find; without that the server does not start, the
client waits out its 20-second timeout (`TimeOutMsNewProcess`) and compiles in its own
process, so the run comes out slower, not faster. So `--shared` sets
`DOTNET_HOST_PATH` and PATH itself.

## What the comparison does NOT account for

The numbers are fair only in the sense that the input is the same. The work is not:

* `csc` runs nullable analysis, definite assignment and control-flow analysis, produces
  the full set of diagnostics and writes attributes; rustlyn does only part of this;
* rustlyn replaces some method bodies with throwing stubs (about 10 of ~61,000 on the
  full corpus); `csc` compiles everything;
* both are multithreaded: on the full corpus `csc` uses about 3.1 cores, rustlyn 2.6
  (its IL generation and metadata writing run on one core);
* neither optimizes IL or writes a PDB;
* `csc` runs as `dotnet csc.dll`, so its time includes CLR startup and JIT of the
  compiler itself (visible on `hello`); rustlyn is a native binary.
