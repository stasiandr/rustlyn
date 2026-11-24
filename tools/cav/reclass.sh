#!/bin/bash
# reclass.sh <results dir> <class prefix>... — reruns the failed tests of the classes with the
# current build binary ($BUILD, default target/fast/examples/build) and prints why each fails.
# The rest of run.sh's environment (DOTNET, FWVER, FW, LANGVERSION) is passed on as it is.
R=$1; shift
CAV_TESTS=${CAV_TESTS:-${CAV_HOME:-/home/user}/cav/tests}
BUILD=${BUILD:-$(dirname "$0")/../../target/fast/examples/build}
for cls in "$@"; do
  for t in $(grep "^$cls" $R/fail.txt | awk '{print $1}'); do
    CAV_TESTS=$CAV_TESTS RESULTS=/tmp/reclass/r OUT=/tmp/reclass/o BUILD=$BUILD "$(dirname "$0")/run.sh" 1 "$t" > /dev/null 2>&1
    if [ -s /tmp/reclass/r/pass.txt ]; then echo "PASS $t"; continue; fi
    kind=$(awk '{print $2}' /tmp/reclass/r/fail.txt)
    if [ "$kind" == "compile" ]; then r=$(grep -v "^wrote" /tmp/reclass/o/$t/build.log | head -3)
    else r=$(cat /tmp/reclass/o/$t/actual.txt 2>/dev/null); fi
    r=$(printf '%s' "$r" | tr -s '[:space:]' ' ')
    e=$(tr -s '[:space:]' ' ' < $CAV_TESTS/$t.expected)
    echo "FAIL $t ($kind): ${r:0:140} || ${e:0:60}"
  done
done
