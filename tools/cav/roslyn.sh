#!/bin/bash
# roslyn.sh [jobs] [glob] — run.sh with the real Roslyn instead of rustlyn: the same tests, options,
# libraries, arguments and comparison, so $RESULTS/{pass,fail}.txt and $OUT/<name>/actual.txt say
# what Roslyn's program prints on this machine (calibrate.sh compares them with rustlyn's).
# Environment as run.sh's, plus CSC (csc.dll; default the SDK beside $DOTNET), ONLY (a file with
# one test name per line). Not translated: `--path k path` (the file name a test gives a source
# is not passed, so a `file` type's name differs); `.il` libraries fail with `ilasm` (no ilasm).
# Called with a source file it is the compiler for run.sh (BUILD): `build`'s command line to csc's.
if [[ $1 == *.cs ]]; then
  source=$1; shift; out=.
  if [ $# -gt 0 ] && [[ $1 != --* ]]; then out=$1; shift; fi
  args=(-shared -nologo -noconfig -nostdlib+ -deterministic+ -debug- -nowarn:CS1701,CS1702,CS8981)
  target=exe; sources=("$source"); lang=preview  # the test harness default: the newest, preview features included
  while [ $# -gt 0 ]; do
    case $1 in
      --references) for d in $2/*.dll; do case $d in *[Nn]ative*|*coreclr*|*clrjit*|*hostpolicy*|*mscordaccore*|*mscordbi*|*clrgc*|*msquic*|*libSystem*|*clretwrc*|*createdump*) ;; *) args+=("-r:$d") ;; esac; done; shift ;;
      --reference) case $2 in
          *=*) for a in $(echo "${2%%=*}" | tr , ' '); do args+=("-r:$a=${2#*=}"); done ;;
          *) args+=("-r:$2") ;; esac; shift ;;
      --library) target=library ;;
      --define) args+=("-define:$2"); shift ;;
      --langversion) lang=$2; shift ;;
      --optimize) args+=(-optimize+) ;;
      --unsafe) args+=(-unsafe+) ;;
      --checked) args+=(-checked+) ;;
      --main) args+=("-main:$2"); shift ;;
      --nullable) args+=("-nullable:$2"); shift ;;
      --source) sources+=("$2"); shift ;;
      --path) shift 2 ;;
      *) echo "roslyn.sh: unknown option $1" >&2; exit 2 ;;
    esac
    shift
  done
  mkdir -p "$out"
  # A language version this csc does not know (the tests' newest, `15`) is the preview one.
  case $lang in 1[5-9]|[2-9][0-9]) lang=preview ;; esac
  csc() { DOTNET_ROOT=$(dirname $DOTNET) DOTNET_CLI_TELEMETRY_OPTOUT=1 $DOTNET $CSC "${args[@]}" "$@" -langversion:$lang -target:$target \
    -out:"$out/$(basename "$source" .cs).dll" "${sources[@]}" | grep -v 'warning'; return ${PIPESTATUS[0]}; }
  # Rustlyn does not insist on /unsafe: a test whose options do not say it gets one retry with it.
  log=$(csc); code=$?
  if [ $code != 0 ] && [[ $log == *CS0227* ]]; then log=$(csc -unsafe+); code=$?; fi
  [ -n "$log" ] && echo "$log"
  exit $code
fi
CAV_HOME=${CAV_HOME:-/home/user}
export DOTNET=${DOTNET:-$CAV_HOME/dotnet/dotnet}
export CSC=${CSC:-$(ls -d $(dirname $DOTNET)/sdk/*/Roslyn/bincore/csc.dll | sort -V | tail -1)}
export BUILD="$(cd "$(dirname "$0")" && pwd)/roslyn.sh"
exec "$(dirname "$0")/run.sh" "$@"
