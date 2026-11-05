#!/bin/bash
# Regenerate the Islaris Coq traces for buri_chez_add.dump with the Islaris
# frontend (dump mode), exactly as Islaris's Makefile does for its examples.
# The traces are isla output: untrusted input that the Islaris proof consumes.
#   gen-traces.sh OUTDIR
#   ISLARIS_ENV  nix-build nix/arm/islaris.nix -A env
#   ISLARIS_SRC  rems-project/islaris c978e10f (for etc/*.toml)
#   ISLA_BIN, ISLA_SNAP, XBIN  see ./isla-footprint
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1
: "${ISLARIS_ENV:?}" "${ISLARIS_SRC:?}" "${ISLA_BIN:?}" "${ISLA_SNAP:?}" "${XBIN:?}"
# 1. The opcode column is the captured bytes (Chez +0x00..+0x23).
bin="$here/../chez/chez1030-buri-arm-add.bin"
want=$(od -An -tx4 -v -N 36 --endian=little "$bin" | tr -s ' \n' '\n' | sed '/^$/d')
got=$(sed -n 's/^ *[0-9a-f]*:\t\([0-9a-f]\{8\}\) .*/\1/p' "$here/buri_chez_add.dump")
[ "$want" = "$got" ] || { echo 'Dump opcodes differ from the captured bytes' >&2; exit 1; }
# 2. Islaris looks for etc/islaris/*.toml under OPAM_SWITCH_PREFIX.
prefix=$(mktemp -d); trap 'rm -rf "$prefix"' EXIT
mkdir -p "$prefix/etc/islaris" && cp "$ISLARIS_SRC"/etc/*.toml "$prefix/etc/islaris/"
export OPAM_SWITCH_PREFIX="$prefix" PATH="$here:$ISLARIS_ENV/bin:$PATH"
islaris "$here/buri_chez_add.dump" -j 2 -o "$out" --coqdir=isla.instructions.buri_chez_add
