#!/bin/bash
# run.sh — binds every extracted diagnostics test with rustlyn and compares what it reports with
# what Roslyn is expected to report (compare.py).
# usage: run.sh [jobs] [glob]   per-test output in $OUT/<name>.actual, the summary in $RESULTS
# Environment: DIAG (default /home/user/diag), DIAG_TESTS (the tests, default $DIAG/tests),
# DIAGNOSE (the `diagnose` example binary), RESULTS and OUT (where to write), FW (the
# reference assemblies: by default the part of the shared framework the tests use).
DIAG=${DIAG:-/home/user/diag}
DIAG_TESTS=${DIAG_TESTS:-$DIAG/tests}
RESULTS=${RESULTS:-$DIAG/results}
OUT=${OUT:-$DIAG/out}
DIAGNOSE=${DIAGNOSE:-$DIAG/diagnose.bin}
if [ -z "$FW" ]; then
  # Reading an assembly costs time on every test, and the tests use little of the framework:
  # netstandard's worth of it is what Roslyn's tests compile against by default.
  FWVER=${FWVER:-$(ls /home/user/dotnet/shared/Microsoft.NETCore.App | sort -V | tail -1)}
  SHARED=/home/user/dotnet/shared/Microsoft.NETCore.App/$FWVER
  FW=$DIAG/fw-$FWVER
  if [ ! -d $FW ]; then
    mkdir -p $FW
    for a in System.Private.CoreLib System.Runtime System.Console System.Collections System.Linq \
             System.Linq.Expressions System.Memory System.ObjectModel System.Runtime.InteropServices \
             System.Threading System.Threading.Tasks Microsoft.CSharp; do
      cp $SHARED/$a.dll $FW/
    done
  fi
fi
rm -rf $RESULTS $OUT; mkdir -p $RESULTS $OUT
one() {
  t=$1; name=$(basename $t .cs); diag=$DIAG_TESTS/$name.diag
  # Roslyn's tests parse at the preview version unless they say otherwise.
  lang=$(sed -n 's/^# langversion: //p' $diag); flags=(--langversion ${lang:-preview})
  grep -q '^# unsafe: true' $diag && flags+=(--unsafe)
  timeout 30 $DIAGNOSE $t --references $FW "${flags[@]}" > $OUT/$name.actual 2> $OUT/$name.err
  code=$?
  if [ $code != 0 ]; then echo "$code" > $OUT/$name.crash; fi
  [ -s $OUT/$name.err ] || rm -f $OUT/$name.err
}
export -f one; export DIAG_TESTS FW DIAGNOSE OUT
# `find`, not a glob: 19 000 paths are more than one command line holds.
find "$DIAG_TESTS" -maxdepth 1 -name "${2:-*}.cs" | sort | xargs -P ${1:-8} -n 1 bash -c 'one "$0"'
python3 "$(dirname "$0")/compare.py" $DIAG_TESTS $OUT $RESULTS "${2:-*}"
