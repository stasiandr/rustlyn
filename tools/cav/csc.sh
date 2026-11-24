#!/bin/bash
# csc.sh — the real C# compiler behind the command line of rustlyn's `build` example, so that
# run.sh can put the same tests through Roslyn: `BUILD=tools/cav/csc.sh tools/cav/run.sh`.
# What passes that way is what the benchmark can fairly ask of rustlyn under the same settings.
# Compiles against the reference pack of $CSC_TFM (default net8.0) from the SDK at $CSC_SDK
# (default $CAV_HOME/dotnet8sdk), through its compiler server; a language version above $CSC_MAX_LANGVERSION (default 11) is
# refused, so that a test written for a newer C# fails here rather than being quietly let through.
# The compiler is that of the framework's own SDK band (8.0.x for net8.0) where the SDK directory
# holds several, the newest one otherwise.
SDK=${CSC_SDK:-${CAV_HOME:-/home/user}/dotnet8sdk}
TFM=${CSC_TFM:-net8.0}
MAX=${CSC_MAX_LANGVERSION:-11}
CSC=$( (ls -d $SDK/sdk/${TFM#net}.*/Roslyn/bincore/csc.dll 2> /dev/null || ls -d $SDK/sdk/*/Roslyn/bincore/csc.dll) | sort -V | tail -1)
PACK=$(ls -d $SDK/packs/Microsoft.NETCore.App.Ref/*/ref/$TFM | sort -V | tail -1)

source=$1; shift
out=.
if [ $# -gt 0 ] && [[ $1 != --* ]]; then out=$1; shift; fi
name=$(basename "$source" .cs)
args=(-shared -nologo -noconfig -nostdlib+ -deterministic+ -debug- -nowarn:CS8981)
for dll in $PACK/*.dll; do args+=("-r:$dll"); done
target=exe; langversion=$MAX
sources=("$source")
while [ $# -gt 0 ]; do
  case $1 in
    --references) shift ;;
    --reference) args+=("-r:$2"); shift ;;
    --library) target=library ;;
    --define) args+=("-define:$2"); shift ;;
    --langversion) langversion=$2; shift ;;
    --optimize) args+=(-optimize+) ;;
    --unsafe) args+=(-unsafe+) ;;
    --checked) args+=(-checked+) ;;
    --main) args+=("-main:$2"); shift ;;
    --source) sources+=("$2"); shift ;;
    --path) shift 2 ;;
    *) echo "csc.sh: unknown option $1" >&2; exit 2 ;;
  esac
  shift
done
case $langversion in
  default|latest|latestmajor) langversion=$MAX ;;
  preview) echo "csc.sh: language version preview is above $MAX" >&2; exit 1 ;;
esac
if [ "$(printf '%s\n%s\n' "$langversion" "$MAX" | sort -V | tail -1)" != "$MAX" ]; then
  echo "csc.sh: language version $langversion is above $MAX" >&2; exit 1
fi
mkdir -p "$out"
exec $SDK/dotnet "$CSC" "${args[@]}" -langversion:$langversion -target:$target \
  -out:"$out/$name.dll" "${sources[@]}"
