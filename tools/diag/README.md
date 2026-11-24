# Diagnostics as a benchmark

`CompileAndVerify` measures half of a compiler: programs that must build and work. The
other half is rejecting a wrong program with the right errors. Roslyn tests of this form
measure it:

```csharp
CreateCompilation(source).VerifyDiagnostics(
    // (6,13): error CS0165: Use of unassigned local variable 'x'
    Diagnostic(ErrorCode.ERR_UseDefViolation, "x").WithArguments("x").WithLocation(6, 13));
```

There are more than forty thousand of them in `roslyn/src/Compilers/CSharp/Test`.
`extract.py` pulls out those that can be reproduced without Roslyn into
`<name>.cs` / `<name>.diag` pairs; `run.sh` binds each file with the `diagnose` example
(parse, declarations, bodies, no emit) and compares what it reported with what the test
expects (`compare.py`).

```sh
python3 tools/diag/extract.py        # → /home/user/diag/tests
cargo build --profile fast -p rustlyn-semantics --example diagnose
cp target/fast/examples/diagnose /home/user/diag/diagnose.bin
tools/diag/run.sh 4                  # → /home/user/diag/results/{summary,errors,warnings}.txt
```

As with `cav/run.sh`, `RESULTS`, `OUT` and `DIAGNOSE` set where to write and what to bind
with, and the second argument is a name mask:

```sh
RESULTS=/tmp/r OUT=/tmp/o DIAGNOSE=target/fast/examples/diagnose tools/diag/run.sh 4 'FlowDiagnosticTests*'
```

## What is extracted

A test is a call to `VerifyDiagnostics` / `VerifyEmitDiagnostics` (or
`GetDiagnostics().Verify`) on a compilation made from **one** source: a literal or a
variable holding a literal. The compilation is a `CreateCompilation(...)` right before
the call, a variable it was assigned to, or `CompileAndVerify(comp)`.
`VerifyDiagnostics()` with no arguments is a test too: a program that must have no
diagnostics at all, and a false error on it is the worst kind of error.

Only tests that mean the same thing against current .NET are taken:

* language no older than C# 12 (`parseOptions` unset or `Regular`, `RegularPreview`,
  `Regular12`…`Regular15`); tests with older versions expect "this feature appeared in
  C# N" errors. The version is written into the header (`# langversion: 14`), and
  `run.sh` passes it to `diagnose`. Without `parseOptions`, Roslyn tests parse as
  **preview** (`TestOptions.RegularPreview` is the default of their `Parse`), and
  `run.sh` does the same: most tests expect preview behaviour, and `Regular` is C# 15.
  The difference shows, for example, with pointers: up to and including C# 15 a pointer
  type outside `unsafe` is CS0214, in preview it is not, and only a dereference gets
  CS9360;
* of the compilation options, only exe/dll, `unsafe` and `nullable`; they are written
  into the `.diag` header (`# kind: exe`, `# unsafe: true`, `# nullable: enable`), and
  `unsafe` is passed as `--unsafe`;
* no references other than the framework (assemblies from IL and second compilations
  are skipped), no `CreateCompilationWithMscorlib40` and `CreateEmptyCompilation`: those
  are about errors for types missing from the old `mscorlib`;
* multiple files, a source assembled from pieces (`source + attr`), and interpolated
  strings are skipped. The exception is a second file that only declares what .NET 10
  already has (`IsExternalInitTypeDefinition`, `CompilerFeatureRequiredAttribute`,
  nullable analysis attributes, `TestSources.Index` and so on): such a file is dropped,
  and the test stays single-file.

Code numbers come from Roslyn's own `ErrorCode.cs`, so any `ErrorCode.ERR_Xxx` becomes
`CSnnnn` without a table on our side. Identical "source + expectation" pairs are written
once. On current Roslyn that is 18,120 tests out of 42,272 calls; `extract.py` prints
how many were skipped and why (`DIAG_VERBOSE='<reason>'` lists those skipped for that
reason).

The `.diag` format: `# key: value` lines, then one expected diagnostic per line,
tab-separated: severity, code, line, column (1-based; `0 0` if the test gave no
location) and the text it points at, as a JSON string. `diagnose` prints the same; it
counts columns in UTF-16 units, as Roslyn does.

References are not the whole shared framework but the part of it in `netstandard`
(CoreLib, `System.Runtime`, `Console`, `Collections`, `Linq`, `Linq.Expressions`,
`Memory`, `ObjectModel`, `InteropServices`, `Threading`, `Threading.Tasks`,
`Microsoft.CSharp`): Roslyn compiles its tests against `netstandard`, and reading an
assembly costs time on every test. `FW` sets a different directory.

## How it is scored

Errors and warnings are compared separately, each in two ways:

* **exact**: the same codes at the same places, as a multiset; an expectation without a
  location matches a diagnostic of the same code on the same text;
* **by code**: the same set of codes, wherever they are.

Errors are the main metric, warnings the secondary one (there is no nullable analysis
yet, and most missing warnings are `CS86xx`). A failed test is tagged with the kind of
mismatch: `spurious`: no errors expected but some reported (the worst); `missing`:
errors expected but none reported; `wrong`: both, but not the same; `crash`: `diagnose`
crashed or exceeded 30 seconds. Besides the score, `summary.txt` lists the codes most
often missing and the codes most often extra, counted by tests rather than occurrences:
that is the work list.
