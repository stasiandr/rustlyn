#!/bin/bash
# consume.sh <Lib> <program.cs> — compiles a program against /home/user/oss/out/<Lib>.dll and runs it
LIB=$1; SRC=$2; FW=/home/user/dotnet/shared/Microsoft.NETCore.App/11.0.0-rc.1.26425.128
REF=/home/user/oss/consume/ref/$LIB; rm -rf $REF; mkdir -p $REF; ln -s $FW/*.dll $REF/ 2>/dev/null; cp /home/user/oss/out/$LIB.dll $REF/
OUT=/home/user/oss/consume/out/$LIB; rm -rf $OUT; mkdir -p $OUT
cd /home/user/rustlyn && ./target/release/examples/build $SRC $OUT --references $REF --define "NET;NETCOREAPP;NET11_0" | grep -v "^wrote" 
name=$(basename $SRC .cs)
cp /home/user/oss/out/$LIB.dll $OUT/
printf '{"runtimeOptions":{"tfm":"net11.0","framework":{"name":"Microsoft.NETCore.App","version":"11.0.0-rc.1.26425.128"}}}' > $OUT/$name.runtimeconfig.json
timeout 60 /home/user/dotnet/dotnet $OUT/$name.dll 2>&1 | head -${3:-20}
