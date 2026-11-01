#!/usr/bin/env bash
# Two-stage x86_64 -> aarch64 build of Chez Scheme 10.3.0, the Chez release
# pinned by shen-scheme v0.52 (Makefile: csversion 10.3.0, archive sha256
# d237d987...).  Configuration mirrors shen-scheme's own:
#   --threads --disable-curses --disable-iconv --disable-x11
# Stage 1 builds a ta6le host Chez from the release's pb boot files and uses it
# to create tarm64le boot files (`make bootquick XM=tarm64le`).  Stage 2 cross
# compiles the tarm64le kernel with the nixpkgs aarch64 cross gcc
# (`configure --cross --force`, per csv10.3.0/BUILDING "CROSS COMPILING").
#
# A single-derivation nix cross build (pkgsCross.aarch64-multiplatform with
# --cross and pb boot files) fails in the host-side pb zlib configure; see
# docs/ARM-FOUNDATION.md.  This script is orchestration only: building
# establishes byte identity, never semantics.
#
# usage: build-chez-10.3.0-aarch64.sh <empty-work-dir>
set -euo pipefail
work=${1:?work dir}
NIX=${NIX:-/nix/var/nix/profiles/default/bin/nix}
tools="$(cd "$(dirname "$0")" && pwd)/tools.nix"   # pinned nixpkgs 885ba4d
path() { "$NIX" build --no-link --print-out-paths -f "$tools" "$1" | grep -v -- '-man$' | head -1; }
HOSTCC=$(path gcc)/bin
MAKE=$(path gnumake)/bin
XCC=$(path aarch64-gcc)/bin
export PATH="$HOSTCC:$MAKE:$XCC:$PATH"
archive=csv10.3.0.tar.gz
want=d237d9874c6e8b0ccf7758daa8286a6e825528b13ce3b2bca56eb1f73cddbc2c
mkdir -p "$work"
cd "$work"
[ -f "$archive" ] || curl -sSL -o "$archive" "https://github.com/cisco/ChezScheme/releases/download/v10.3.0/$archive"
echo "$want  $archive" | sha256sum -c -
rm -rf host target
mkdir host target
tar xzf "$archive" -C host
tar xzf "$archive" -C target
flags=(--threads --disable-curses --disable-iconv --disable-x11)
( cd host/csv10.3.0 && ./configure "${flags[@]}" && make -j"${JOBS:-4}" && make bootquick XM=tarm64le )
cp -r host/csv10.3.0/boot/tarm64le target/csv10.3.0/boot/
( cd target/csv10.3.0 && ./configure --cross --force -m=tarm64le "${flags[@]}" \
    --toolprefix=aarch64-unknown-linux-gnu- CC_FOR_BUILD=gcc && make -j"${JOBS:-4}" )
sha256sum target/csv10.3.0/tarm64le/bin/tarm64le/scheme \
          target/csv10.3.0/tarm64le/boot/tarm64le/petite.boot \
          target/csv10.3.0/tarm64le/boot/tarm64le/scheme.boot
