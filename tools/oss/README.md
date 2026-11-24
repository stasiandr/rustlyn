# Open-source libraries as a corpus

`build.sh` binds and builds one library from source (with the same `/define:` symbols as
its `.csproj`); `run_all.sh` does all eight: Newtonsoft.Json, Serilog, Humanizer, Dapper,
NodaTime, MoreLINQ, FluentValidation, Polly. Libraries whose `.csproj` enables implicit
usings get them from `implicit/<Name>.g.cs`. The result is `/home/user/oss/out/<Name>.dll`
with `<Name>.stubs.txt` next to it, listing the bodies replaced by a stub and why.

`consume/consume.sh <Name> <program.cs>` builds a program against the built library and
runs it; the programs in `consume/` are small usage scenarios: serializing and parsing
JSON, writing logs, working with dates, LINQ extensions, retry policies. A program's name
must not match the library's assembly name.

Paths in the scripts are `/home/user/oss/<repository>` and `/home/user/dotnet`.
