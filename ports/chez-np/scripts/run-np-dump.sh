#!/bin/sh
# Reproduce ports/chez-np/*-buri-arm-add.np (orchestration only).
# Needs the Chez 10.3.0 builds made by nix/arm/build-chez-10.3.0-aarch64.sh:
#   HOST   = <work>/host/csv10.3.0/ta6le        (stage 1, x86_64)
#   TARGET = <work>/target/csv10.3.0/tarm64le   (stage 2, aarch64; run under qemu-user)
# usage: run-np-dump.sh HOST TARGET QEMU-AARCH64 OUT-DIR
set -eu
host=$1 target=$2 qemu=$3 out=$4
here=$(cd "$(dirname "$0")" && pwd)
"$host/bin/ta6le/scheme" -b "$host/boot/ta6le/petite.boot" -b "$host/boot/ta6le/scheme.boot" \
  -q --script "$here/np-dump.ss" "$out/ta6le-buri-arm-add.np"
"$qemu" "$target/bin/tarm64le/scheme" -b "$target/boot/tarm64le/petite.boot" \
  -b "$target/boot/tarm64le/scheme.boot" -q --script "$here/np-dump.ss" "$out/tarm64le-buri-arm-add.np"
