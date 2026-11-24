#!/bin/bash
# scope.sh — the part of the benchmark a target asks for: the tests that Roslyn itself
# compiles under that language version against that framework and that then print what they
# should. They are linked into $SCOPE/tests, their names listed in $SCOPE/scope.txt, and run.sh
# measures rustlyn on them with the same settings:
#
#   tools/cav/scope.sh                      # C# 11 on net8.0 into $CAV_HOME/cav11
#   CAV_TESTS=$SCOPE/tests DOTNET=$CSC_SDK/dotnet LANGVERSION=11 tools/cav/run.sh
#
# Environment: CAV_HOME (default /home/user), CAV_TESTS (every extracted test, default
# $CAV_HOME/cav/tests), SCOPE, FWVER (the runtime the programs run on, by default the newest of the
# target's version beside $CSC_SDK/dotnet), and those of csc.sh: CSC_SDK (an SDK that has the
# framework's reference pack and runtime, such as a system-wide /usr/local/share/dotnet with
# several), CSC_TFM, CSC_MAX_LANGVERSION.
set -e
cd "$(dirname "$0")/../.."
CAV_HOME=${CAV_HOME:-/home/user}
export CSC_SDK=${CSC_SDK:-$CAV_HOME/dotnet8sdk}
export CSC_TFM=${CSC_TFM:-net8.0}
export CSC_MAX_LANGVERSION=${CSC_MAX_LANGVERSION:-11}
ALL=${CAV_TESTS:-$CAV_HOME/cav/tests}
SCOPE=${SCOPE:-$CAV_HOME/cav${CSC_MAX_LANGVERSION%%.*}}
if [ ! -x $CSC_SDK/dotnet ]; then
  curl -sSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh
  bash /tmp/dotnet-install.sh --channel ${CSC_TFM#net} --install-dir $CSC_SDK > /dev/null
fi
export FWVER=${FWVER:-$(ls $CSC_SDK/shared/Microsoft.NETCore.App | grep "^${CSC_TFM#net}\." | sort -V | tail -1)}
CAV_TESTS=$ALL RESULTS=$SCOPE/csc-r OUT=$SCOPE/csc-o BUILD=$PWD/tools/cav/csc.sh \
  DOTNET=$CSC_SDK/dotnet tools/cav/run.sh "${1:-$(getconf _NPROCESSORS_ONLN)}"
rm -rf $SCOPE/tests; mkdir -p $SCOPE/tests
sort $SCOPE/csc-r/pass.txt > $SCOPE/scope.txt
# Every file of a test is <name>.<something>: its parts, libraries, options and expectation.
(cd $ALL && find . -maxdepth 1 -type f) | sed 's|^\./||' | awk -v dir=$ALL '
  NR == FNR { keep[$1] = 1; next }
  { name = $0; sub(/\.(ref[0-9]+\.)?(part[0-9]+\.)?[a-z]+$/, "", name)
    if (name in keep) print dir "/" $0 }' $SCOPE/scope.txt - | xargs sh -c '[ $# -eq 0 ] || ln -sf "$@" "$0"' $SCOPE/tests
echo "in scope: $(awk 'END { print NR }' $SCOPE/scope.txt) of $(find $ALL -maxdepth 1 -name '*.expected' | awk 'END { print NR }')"
