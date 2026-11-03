#!/bin/sh
# Reproduce ports/chez-np/tarm64le-buri-arm-add.raw.np (orchestration only).
#   PATCHED = OUT-DIR/csv10.3.0 of build-patched-chez.sh
#   SCHEME  = the stock tarm64le kernel binary (sha256 21900313..., ports/arm/README.md)
# usage: run-np-dump-raw.sh PATCHED SCHEME QEMU-AARCH64 OUT-DIR
set -eu
patched=$1 scheme=$2 qemu=$3 out=$4
here=$(cd "$(dirname "$0")" && pwd)
echo "219003131938590d5828635e1ae5bd5e57feb8080bdb4c1dfdfa7f2f8f4be390  $scheme" | sha256sum -c -
"$qemu" "$scheme" -b "$patched/boot/tarm64le/petite.boot" -b "$patched/boot/tarm64le/scheme.boot" \
  -q --script "$here/np-dump-raw.ss" "$out/tarm64le-buri-arm-add.raw.np"
