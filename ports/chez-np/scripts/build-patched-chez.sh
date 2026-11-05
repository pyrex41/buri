#!/bin/sh
# Build the trusted IR-dumping tool of docs/CHEZ-NANOPASS.md section 8
# (orchestration only; building establishes byte identity, never semantics).
#
# Input: the stage-1 x86_64 host tree made by nix/arm/build-chez-10.3.0-aarch64.sh
# (<work>/host/csv10.3.0, already built).  The script copies it, checks and
# applies ports/chez-np/patches/np-trace-raw.patch (one change to the tracer's
# ir-printer in s/cpnanopass.ss), rebuilds the host and regenerates the
# tarm64le boot files with `make bootquick XM=tarm64le`.  The C kernel is not
# rebuilt: the stock tarm64le `scheme` binary of the same build runs the
# patched boot files.  gcc and gnumake must be on PATH (the pinned ones from
# nix/arm/tools.nix were used).
#
# usage: build-patched-chez.sh HOST-TREE OUT-DIR
set -eu
src=$1 out=$2
here=$(cd "$(dirname "$0")/.." && pwd)
patch_sha=42b81e388082dc38258fe2dad2a9b39d04ee16ef8a98bdce8b3a7259ce00749e
echo "$patch_sha  $here/patches/np-trace-raw.patch" | sha256sum -c -
rm -rf "$out"
mkdir -p "$out"
cp -a "$src" "$out/csv10.3.0"
cd "$out/csv10.3.0"
echo "2377a95116057ab940d4bd9864ed5ec5e1995fca5741ebf394f3933cec139dcd  s/cpnanopass.ss" | sha256sum -c -
patch -p1 < "$here/patches/np-trace-raw.patch"
echo "5983da2334967af289fe4be4e14bab0c6faf47f42d79e5c0ffbb971874cb1d29  s/cpnanopass.ss" | sha256sum -c -
make -j"${JOBS:-3}"
rm -f boot/tarm64le/petite.boot boot/tarm64le/scheme.boot
make bootquick XM=tarm64le
sha256sum boot/tarm64le/petite.boot boot/tarm64le/scheme.boot
