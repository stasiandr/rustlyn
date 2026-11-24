#!/bin/bash
# build.sh <name> <source dir> <defines> — binds and assembles an open-source library with rustlyn
NAME=$1; DIR=/home/user/oss/$2; DEFS="NET;NETCOREAPP;NET11_0;NET11_0_OR_GREATER;NET10_0_OR_GREATER;NET9_0_OR_GREATER;NET8_0_OR_GREATER;NET7_0_OR_GREATER;NET6_0_OR_GREATER;NET5_0_OR_GREATER;NETCOREAPP3_1_OR_GREATER;NETCOREAPP3_0_OR_GREATER;NETCOREAPP2_1_OR_GREATER;NETCOREAPP2_0_OR_GREATER;$3"
FW=/home/user/dotnet/shared/Microsoft.NETCore.App/11.0.0-rc.1.26425.128
OUT=/home/user/oss/out; mkdir -p $OUT
cd /home/user/rustlyn
files() { ls /home/user/oss/implicit/$NAME.g.cs 2>/dev/null; find $DIR -name '*.cs' -not -path '*/obj/*' -not -path '*/bin/*' | sort; }
echo "=== $NAME: $(files | wc -l) files"
files | ./target/release/examples/bind $FW --define "$DEFS" 2>&1 | grep -v "^\s*$" | head -14
files | ./target/release/examples/assemble $FW $OUT/$NAME.dll --define "$DEFS" 2>&1 | tail -3
[ -f $OUT/$NAME.stubs.txt ] && { echo "stubs: $(wc -l < $OUT/$NAME.stubs.txt)"; cut -f2 $OUT/$NAME.stubs.txt | sort | uniq -c | sort -rn | head -8; }
