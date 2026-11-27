# CompileAndVerify as a benchmark

Roslyn tests of the form `CompileAndVerify(source, expectedOutput: "...")` are
thousands of small programs with known output, written by people who knew where
compilers go wrong. `extract.py` pulls them out of `roslyn/src/Compilers/CSharp/Test`
into `<name>.cs` / `<name>.expected` pairs, `run.sh` builds each with our `build`, runs
it on the real runtime and compares the output (whitespace normalized), and
`reclass.sh` reruns the failed tests of selected classes with the current build and
prints the reason.

Paths in the scripts default to one root: everything lives under `$CAV_HOME` (default
`/home/user`): `roslyn`, `cav`, `dotnet`, `ilasm` (the runtime version is the latest
installed, or `FWVER`). The scripts also run on macOS (bash 3.2, BSD utilities): where
there is no `timeout`, perl's `alarm` limits the time.

What is extracted is what the Roslyn test actually compiles, not the first literal in
sight: `extract.py` evaluates the test's C# expressions: string concatenation, constants
of the test class and test utilities (`IsExternalInitTypeDefinition`,
`Buffer10Definition`, `TestResources` resources), `Environment.NewLine`, interpolation,
`switch` expressions, wrappers like `ExpectedOutput(...)` and
`ExecutionConditionUtil.IsMonoOrCoreClr ? ... : null` (the machine is .NET on Linux),
variables assigned before the call, the compilation handed to the call
(`var comp = CreateCompilation(source, options: ...)`), and the test's helper methods
that return an expression. A theory (`[Theory]`) gives one test per `[InlineData]` row
or per combination of `bool` parameters of `[CombinatorialData]`; a call under an `if`
that the theory row does not take is not extracted. A helper method with parameters that
contains `CompileAndVerify` is extracted once per call from the test, with parameters
bound to that call's arguments (`<class>_<test>_<method><call number>_<k>`), and a call
inside a `foreach` over a list written in the test once per element (`_<number>` at the
end). A test where something cannot be evaluated (IL that is not a literal, expected
output `null`, runtime async) is skipped; `CAV_VERBOSE=1` prints which and why,
`CAV_ONLY='RecordTests|InlineArrayTests'` extracts only those classes.

A test is named `<class>_<method>_<k>`: k is the number of the `CompileAndVerify` call in
the method, with `_<row>` added for a theory. The name does not depend on what is
extracted in other tests, so it stays the same whatever the script learns.

Besides `<name>.cs` and `<name>.expected` a test can have:

* `<name>.part1.cs`, …: the other files of the same compilation
  (`new[] { source, IsExternalInitTypeDefinition }`), passed to `build` with `--source`;
* `<name>.options`: `build` options one per line: `--langversion 9` (from
  `parseOptions: TestOptions.Regular9`), `--optimize` (`ReleaseExe`, which is what
  `CompileAndVerify` does by default), `--main C` (`WithMainTypeName`), `--checked`,
  `--unsafe`, `--define A;B` (`WithPreprocessorSymbols`), and `--path k path`, the path
  the test gave file k (empty if it gave none: `file` type names are hashed from it);
* `<name>.args` and `<name>.exitcode`: the program's command-line arguments (`args:`)
  and the code it must exit with (`expectedReturnCode:`);
* `<name>.ref0.cs`, …: libraries, see below, with their own `.part` and `.options`
  files.

```sh
python3 tools/cav/extract.py          # → /home/user/cav/tests
cp target/release/examples/build /home/user/cav/build.bin
tools/cav/run.sh 6                    # → /home/user/cav/results/{pass,fail}.txt
tools/cav/reclass.sh /home/user/cav/results CodeGenTupleTest RecordTests   # failure reasons
```

Several runs can share the same tests: `RESULTS`, `OUT` and `BUILD` set where to write
and what to build with, and the second argument is a name mask:

```sh
RESULTS=/tmp/r OUT=/tmp/o BUILD=target/release/examples/build tools/cav/run.sh 4 'RecordTests*'
```

A test compiled against another C# compilation
(`references: new[] { lib.EmitToImageReference() }`) gets that compilation's source next
to it: `<name>.ref0.cs`, `<name>.ref1.cs`, … in build order. `run.sh` builds each library
(`build --library`, referencing the previous ones with `--reference`), then the test
against them. A reference built from IL (`CompileIL`, `CreateCompilationWithIL`) is
extracted as `<name>.ref<k>.il` and assembled with `ilasm` (`ILASM`, default
`/home/user/ilasm/ilasm`, installed by `setup.sh`); a first line `// cav-ilasm: ...`
holds its switches. Tests whose IL is not a literal are skipped. A library the test
references under an `extern alias` (`ToMetadataReference(aliases: ...)`,
`.WithAliases(...)`) starts with a line `// cav-aliases: A,B`, and `run.sh` passes it as
`--reference A,B=lib.dll`.

A test whose options name an entry point type (`WithMainTypeName("C")`) gets a
`<name>.main` next to it, and `run.sh` passes that name to `build` as `--main C`; a test
run with arguments (`args: new[] { ... }`) gets `<name>.args`, one argument per line; and
one parsed with extra symbols (`WithPreprocessorSymbols("DEBUG")`) gets `<name>.define`.
A source to which the test appends a string constant of its class
(`@"..." + DisposableClass`) is extracted together with it.

`CAV_TESTS` sets the test directory for both scripts:

```sh
CAV_TESTS=/home/user/cav-multi/tests python3 tools/cav/extract.py
CAV_TESTS=/home/user/cav-multi/tests RESULTS=/tmp/r OUT=/tmp/o BUILD=target/release/examples/build tools/cav/run.sh 4
```

On a fresh machine `tools/cav/setup.sh` does all of this: installs .NET 10 into
`/home/user/dotnet`, clones Roslyn, extracts the tests and runs them once to have a
baseline (`/home/user/cav/results`). It leaves an already extracted test directory
alone: after changing `extract.py`, remove the old `tests` and `results` to extract
again and compare against a baseline of the same extraction. For iterating, build the
compiler with the `fast` profile (`target/fast/examples/build`): a change in `body.rs`
rebuilds in seconds rather than a minute, and a test compiles almost as fast as with a
`release` build.

`CodeGenFunctionPointersTests` go through their own helpers
`CompileAndVerifyFunctionPointers` (an unsafe program in the preview language) and
`CompileAndVerifyFunctionPointersWithIl`, which the main extraction does not see.
`CAV_CALL` (a regular expression) replaces the call name; extract them into a separate
directory so as not to shift call numbers in the methods of the main set:

```sh
CAV_TESTS=/home/user/cav-fp/tests CAV_CALL='CompileAndVerifyFunctionPointers(?:WithIl)?' python3 tools/cav/extract.py
CAV_TESTS=/home/user/cav-fp/tests RESULTS=/tmp/r OUT=/tmp/o BUILD=target/fast/examples/build tools/cav/run.sh 4
```

To hunt for bugs in one area rather than measure the overall benchmark, `extract_more.py`
pulls more tests out of selected files: programs made of several sources
(`[source, s_collectionExtensions]`), sources from constants of the test class and
`CSharpTestBase`, raw strings, and `IncludeExpectedOutput(...)`. It does not change the
baseline run:

```sh
CAV_TESTS=/home/user/cav-more/tests python3 tools/cav/extract_more.py '**/UnionsTests.cs' '**/CollectionExpressionTests*.cs'
CAV_TESTS=/home/user/cav-more/tests RESULTS=/tmp/r OUT=/tmp/o BUILD=target/fast/examples/build tools/cav/run.sh 8
```

## Calibration: which failures are real

An `output` or `runtime` failure is not always a bug of ours: the expectation may have been
written for .NET Framework (an expression tree printed as `ConvertChecked(arg)` rather than
`ConvertChecked(arg, Int32)`), for Windows or for another culture. `roslyn.sh` is `run.sh` with
the real `csc` of the SDK beside `DOTNET` (`CSC` names another) in place of `build`: same tests,
options, libraries, arguments and comparison, results in `$RESULTS`/`$OUT`, and `ONLY=<file>` (also
understood by `run.sh`) restricts either to the test names in a file, one per line. A test without
`--langversion` is compiled with `preview`, as the Roslyn tests are; `15`, which this csc does not
know, becomes `preview`, and a test that fails for want of `/unsafe` is retried with it, since we do
not insist on it. `--path` is not passed (the names of `file` types differ), and tests with an `.il`
library fail with `ilasm`, there being none.

```sh
awk '$2 != "compile" && $2 != "ilasm" { print $1 }' /home/user/cav/results/fail.txt > /tmp/failed.txt
DOTNET=/opt/dotnet/dotnet ONLY=/tmp/failed.txt RESULTS=/tmp/lr OUT=/tmp/lr/out tools/cav/roslyn.sh 2
tools/cav/calibrate.sh /home/user/cav/results /tmp/lr   # → /home/user/cav/results/calibrated.txt
```

`calibrate.sh` writes `<name> <reason> <verdict>` for every failure and prints a summary by class.
`real`: Roslyn's program prints what the test expects, ours does not. `environment-same` /
`environment-differs`: Roslyn's program does not print it either, and ours prints the same /
something else than Roslyn's (so `environment-differs` is worth a look). `environment-nocompile`:
Roslyn does not compile the test against these assemblies; `skipped`: needs ilasm; `unknown`:
roslyn.sh did not run it.

## Target: C# 11 on net8.0

The parity measure is not all extracted tests but those that matter for projects
targeting `<TargetFramework>net8.0</TargetFramework>` with `<LangVersion>11</LangVersion>`.
Roslyn itself separates them: `scope.sh` runs every test through the real `csc` (`csc.sh`
wraps it with `build`'s command line) with `-langversion:11` against the net8.0
reference assemblies and runs it on .NET 8. Whatever passes is the target: a test of
C# 12+ features does not compile here and does not count, and neither does an
expectation Roslyn itself does not meet on net8.0.

```sh
tools/cav/scope.sh                         # → /home/user/cav11/{scope.txt,tests}
CAV_TESTS=/home/user/cav11/tests DOTNET=/home/user/dotnet8sdk/dotnet LANGVERSION=11 \
  RESULTS=/tmp/r OUT=/tmp/o BUILD=target/fast/examples/build tools/cav/run.sh
```

On a Mac where SDK 8.0 is already installed next to others (`/usr/local/share/dotnet`),
`CSC_SDK` names it: the compiler is taken from the 8.0 SDK band, programs run on the 8.0
runtime (`FWVER`), and rustlyn is more fairly built against the same ref pack as csc,
the way a `net8.0` project is built:

```sh
export CAV_HOME=/path/to/cav-work CSC_SDK=/usr/local/share/dotnet
tools/cav/scope.sh 16                      # → $CAV_HOME/cav11/{scope.txt,tests}
CAV_TESTS=$CAV_HOME/cav11/tests DOTNET=$CSC_SDK/dotnet FWVER=8.0.31 LANGVERSION=11 \
  FW=$CSC_SDK/packs/Microsoft.NETCore.App.Ref/8.0.31/ref/net8.0 \
  RESULTS=/tmp/r OUT=/tmp/o BUILD=target/fast/examples/build tools/cav/run.sh 16
```

On Roslyn 90083ecf (26 September 2026) that is 7,581 tests out of 16,939 (csc 8.0.425,
runtime 8.0.31), and rustlyn passes 5,960 of them (78.6%). Most failures are in C# 10
interpolated string handlers (514), C# 8 default interface implementations (263), one
`goto case` theory in a pattern `switch` (172), and async iterators (about 120).
