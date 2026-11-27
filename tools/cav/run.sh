#!/bin/bash
# run.sh — compiles every extracted CompileAndVerify test with rustlyn, runs it, and compares the output.
# usage: run.sh [jobs] [glob]   results in $RESULTS/{pass,fail}.txt and per-test logs in $OUT
# A test <name>.cs with libraries <name>.ref0.cs, <name>.ref1.cs, ... is built after them, each
# library against the ones before it, and runs with their dlls beside it. The other files of a
# compilation (<name>.part1.cs, ..., <name>.ref0.part1.cs, ...) are built with it, and its
# options (<name>.options, <name>.ref0.options: one command-line argument per line) passed on;
# the program runs with the arguments of <name>.args and has to exit with <name>.exitcode.
# A library whose first line is `// cav-aliases: A,B` is referenced as `extern alias` A and B.
# A library <name>.ref<k>.il is assembled with ilasm, with the flags its first line
# `// cav-ilasm: ...` gives.
# ONLY=<file> restricts the run to the test names (one per line) in that file.
# Runs under bash 3.2 and BSD tools (macOS) as well as on Linux: `timeout` falls back to perl's alarm.
# Environment: CAV_HOME (where the rest lives by default: /home/user), CAV, CAV_TESTS (the tests,
# default $CAV/tests), BUILD (the `build` example binary),
# RESULTS and OUT (where to write, so that several runs can share the tests), FWVER, FW (the
# assemblies to compile against, by default the runtime's own: a reference pack such as net8.0's
# works too), ILASM, DOTNET (the host that runs the programs; the framework is looked up beside it)
# and LANGVERSION (the language version a test is compiled with when its options do not name one).
CAV_HOME=${CAV_HOME:-/home/user}
CAV=${CAV:-$CAV_HOME/cav}
CAV_TESTS=${CAV_TESTS:-$CAV/tests}
RESULTS=${RESULTS:-$CAV/results}
OUT=${OUT:-$CAV/out}
DOTNET=${DOTNET:-$CAV_HOME/dotnet/dotnet}
FWVER=${FWVER:-$(ls $(dirname $DOTNET)/shared/Microsoft.NETCore.App | sort -V | tail -1)}
FW=${FW:-$(dirname $DOTNET)/shared/Microsoft.NETCore.App/$FWVER}
TFM=net${FWVER%%.*}.0
BUILD=${BUILD:-$CAV/build.bin}
ILASM=${ILASM:-$CAV_HOME/ilasm/ilasm}
rm -rf $RESULTS $OUT; mkdir -p $RESULTS $OUT; touch $RESULTS/pass.txt $RESULTS/fail.txt
# On macOS .NET 10 formats numbers by the region the system settings name (`1,5` under a
# Georgian one) unless the environment names a locale; the expected output is en-US's.
[ "$(uname -s)" == Darwin ] && export LC_ALL=${LC_ALL:-en_US.UTF-8}
# `limit <seconds> <command>...`: GNU timeout, or where there is none (macOS) perl's alarm, whose
# SIGALRM is reported as timeout's 124.
if command -v timeout > /dev/null; then limit() { timeout "$@"; }
else limit() { perl -e 'alarm shift; exec @ARGV or exit 127' "$@"; local code=$?; [ $code == 142 ] && code=124; return $code; }
fi
# `lines <array> <command>...`: the command's output, a line per element (mapfile before bash 4).
lines() { local _name=$1 _line; shift; eval "$_name=()"; while IFS= read -r _line || [ -n "$_line" ]; do eval "$_name+=(\"\$_line\")"; done < <("$@"); }
# The arguments that build <base>.cs: its other files and its options.
args_of() {
  local base=$1 j=1
  while [ -f $base.part$j.cs ]; do printf '%s\n' --source $base.part$j.cs; j=$((j + 1)); done
  [ -f $base.options ] && cat $base.options
  if [ -n "$LANGVERSION" ] && ! grep -qx -- --langversion $base.options 2>/dev/null; then
    printf '%s\n' --langversion $LANGVERSION
  fi
}
one() {
  t=$1; name=$(basename $t .cs); dir=$OUT/$name; mkdir -p $dir
  refs=(); k=0
  while [ -f $CAV_TESTS/$name.ref$k.cs ] || [ -f $CAV_TESTS/$name.ref$k.il ]; do
    if [ -f $CAV_TESTS/$name.ref$k.il ]; then
      il=$CAV_TESTS/$name.ref$k.il
      flags=$(head -1 $il | sed -n 's|^// cav-ilasm:||p')
      if ! limit 60 $ILASM -dll -quiet $flags -output=$dir/$name.ref$k.dll $il >> $dir/build.log 2>&1; then
        echo "$name ilasm" >> $RESULTS/fail.txt; return
      fi
      # The runtime looks for an assembly by the name it declares.
      declared=$(sed -En "s/^[[:space:]]*\.assembly[[:space:]]+'?([^' {]*)'?[[:space:]]*\{?.*/\1/p" $il | grep -v '^extern$' | head -1)
      [ -n "$declared" ] && [ "$declared" != "$name.ref$k" ] && cp $dir/$name.ref$k.dll $dir/$declared.dll
      refs+=(--reference $dir/$name.ref$k.dll); k=$((k + 1)); continue
    fi
    lines extra args_of $CAV_TESTS/$name.ref$k
    if ! limit 60 $BUILD $CAV_TESTS/$name.ref$k.cs $dir --references $FW "${refs[@]}" --library --define "NET;NETCOREAPP;NET${FWVER%%.*}_0" "${extra[@]}" >> $dir/build.log 2>&1; then
      echo "$name compile" >> $RESULTS/fail.txt; return
    fi
    # A library marked `// cav-aliases: A,B` is referenced under those `extern alias`es.
    aliases=$(head -1 $CAV_TESTS/$name.ref$k.cs | sed -n 's|^// cav-aliases: ||p')
    refs+=(--reference ${aliases:+$aliases=}$dir/$name.ref$k.dll); k=$((k + 1))
  done
  lines extra args_of $CAV_TESTS/$name
  if ! limit 60 $BUILD $t $dir --references $FW "${refs[@]}" --define "NET;NETCOREAPP;NET${FWVER%%.*}_0" "${extra[@]}" >> $dir/build.log 2>&1; then
    echo "$name compile" >> $RESULTS/fail.txt; return
  fi
  printf '{"runtimeOptions":{"tfm":"%s","framework":{"name":"Microsoft.NETCore.App","version":"%s"}}}' $TFM $FWVER > $dir/$name.runtimeconfig.json
  runargs=(); [ -f $CAV_TESTS/$name.args ] && lines runargs cat $CAV_TESTS/$name.args
  actual=$(limit 20 $DOTNET $dir/$name.dll "${runargs[@]}" 2>&1 < /dev/null; echo "exit=$?")
  code=${actual##*exit=}; actual=${actual%exit=*}
  norm() { tr -s '[:space:]' ' ' | sed 's/^ //; s/ $//'; }
  # The exit code counts only where the test names one.
  exited=ok; [ -f $CAV_TESTS/$name.exitcode ] && [ "$code" != "$(cat $CAV_TESTS/$name.exitcode)" ] && exited=wrong
  if [ "$exited" == ok ] && [ "$(printf '%s' "$actual" | norm)" == "$(cat $CAV_TESTS/$name.expected | norm)" ]; then
    echo "$name" >> $RESULTS/pass.txt
  else
    printf '%s' "$actual" > $dir/actual.txt
    if [ "$code" == "124" ]; then echo "$name timeout" >> $RESULTS/fail.txt
    elif printf '%s' "$actual" | grep -Eq "Unhandled exception|InvalidProgramException|BadImageFormat"; then echo "$name runtime" >> $RESULTS/fail.txt
    else echo "$name output" >> $RESULTS/fail.txt; fi
  fi
}
export -f one args_of limit lines; export CAV CAV_TESTS FW BUILD FWVER TFM RESULTS OUT ILASM DOTNET LANGVERSION
find $CAV_TESTS -maxdepth 1 -name "${2:-*}.cs" | grep -Ev '\.(ref|part)[0-9]*\.cs$' | { if [ -n "$ONLY" ]; then grep -Fxf <(sed "s|^|$CAV_TESTS/|; s|\$|.cs|" $ONLY); else cat; fi; } | xargs -P ${1:-8} -n 1 bash -c 'one "$0"'
pass=$(awk 'END { print NR }' $RESULTS/pass.txt); fail=$(awk 'END { print NR }' $RESULTS/fail.txt)
echo "pass: $pass  fail: $fail  ($(( 100 * pass / (pass + fail) ))%)"
awk '{print $2}' $RESULTS/fail.txt | sort | uniq -c | sort -rn
