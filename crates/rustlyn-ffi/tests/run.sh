#!/bin/bash
# Compiles `header.c` against the real library and runs it.
#
# The header is written by hand, so only a C compiler can say whether it
# describes the library. This is that compiler.
set -euo pipefail
cd "$(dirname "$0")"

CRATE="$(cd ../.. && pwd)"
WORKSPACE="$(cd "$CRATE/.." && pwd)"

echo "==> cargo build --release -p rustlyn-ffi"
cargo build --release -p rustlyn-ffi --manifest-path "$WORKSPACE/Cargo.toml"

LIB="$WORKSPACE/target/release/librustlyn_ffi.a"
[[ -f "$LIB" ]] || { echo "no static library at $LIB" >&2; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# The static library needs the platform's own libraries behind it: Rust's
# standard library calls into libc, the threading library and libm.
case "$(uname -s)" in
    Darwin) SYSTEM=(-framework CoreFoundation -lSystem -lresolv -liconv -lc++) ;;
    *)      SYSTEM=(-lpthread -ldl -lm) ;;
esac

echo "==> cc header.c"
cc -std=c11 -Wall -Wextra -Werror -I ../include \
   header.c "$LIB" "${SYSTEM[@]}" -o "$WORK/header"

echo "==> run"
"$WORK/header" "$WORK"
