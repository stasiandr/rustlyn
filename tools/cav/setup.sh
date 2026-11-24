#!/bin/bash
# setup.sh — prepares a fresh machine for the CompileAndVerify benchmark:
# the .NET runtime in $CAV_HOME/dotnet, ilasm in $CAV_HOME/ilasm, Roslyn's sources in $CAV_HOME/roslyn,
# the extracted tests in $CAV_HOME/cav/tests, the target's part of them (C# 11 on net8.0, the
# tests Roslyn itself passes there: see scope.sh) in $CAV_HOME/cav11 and a baseline run of it in
# $CAV_HOME/cav11/results (so that a change can be compared with what passed before it).
# CAV_HOME is /home/user unless set; CSC_SDK (default $CAV_HOME/dotnet8sdk) may name an SDK
# already installed, such as /usr/local/share/dotnet on a Mac that has the 8.0 SDK in it.
# Idempotent: whatever is already there is kept.
# usage: tools/cav/setup.sh [jobs]
set -e
cd "$(dirname "$0")/../.."
export CAV_HOME=${CAV_HOME:-/home/user}
export CSC_SDK=${CSC_SDK:-$CAV_HOME/dotnet8sdk}
JOBS=${1:-$(getconf _NPROCESSORS_ONLN)}
if [ ! -x $CAV_HOME/dotnet/dotnet ]; then
  curl -sSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh
  bash /tmp/dotnet-install.sh --channel 10.0 --install-dir $CAV_HOME/dotnet > /dev/null
fi
# ilasm, for the tests whose references are written in IL.
if [ ! -x $CAV_HOME/ilasm/ilasm ]; then
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) rid=osx-arm64 ;; Darwin-*) rid=osx-x64 ;;
    Linux-aarch64) rid=linux-arm64 ;; *) rid=linux-x64 ;;
  esac
  mkdir -p $CAV_HOME/ilasm
  curl -sSL -o $CAV_HOME/ilasm/ilasm.nupkg \
    https://api.nuget.org/v3-flatcontainer/runtime.$rid.microsoft.netcore.ilasm/10.0.12/runtime.$rid.microsoft.netcore.ilasm.10.0.12.nupkg
  python3 -c "import zipfile, sys; zipfile.ZipFile(sys.argv[1] + '/ilasm.nupkg').extractall(sys.argv[1] + '/pkg')" $CAV_HOME/ilasm
  chmod +x $CAV_HOME/ilasm/pkg/runtimes/$rid/native/ilasm
  ln -sf $CAV_HOME/ilasm/pkg/runtimes/$rid/native/ilasm $CAV_HOME/ilasm/ilasm
fi
if [ ! -d $CAV_HOME/roslyn/src ]; then
  git clone -q --depth 1 https://github.com/dotnet/roslyn.git $CAV_HOME/roslyn
fi
if [ ! -d $CAV_HOME/cav/tests ]; then
  python3 tools/cav/extract.py
fi
cargo build --profile fast -p rustlyn-emit --example build
if [ ! -f $CAV_HOME/cav11/scope.txt ]; then
  tools/cav/scope.sh "$JOBS"
fi
if [ ! -f $CAV_HOME/cav11/results/pass.txt ]; then
  cp target/fast/examples/build $CAV_HOME/cav11/baseline.bin
  FWVER=${FWVER:-$(ls $CSC_SDK/shared/Microsoft.NETCore.App | grep '^8\.0\.' | sort -V | tail -1)} \
  CAV_TESTS=$CAV_HOME/cav11/tests RESULTS=$CAV_HOME/cav11/results OUT=$CAV_HOME/cav11/out \
    BUILD=$CAV_HOME/cav11/baseline.bin DOTNET=$CSC_SDK/dotnet LANGVERSION=11 \
    tools/cav/run.sh "$JOBS"
fi
echo "ready: $(awk 'END { print NR }' $CAV_HOME/cav11/results/pass.txt) of $(awk 'END { print NR }' $CAV_HOME/cav11/scope.txt) tests pass at baseline"
