#!/bin/bash
# Opt-in check of ports/arm/islaris/buri_chez_add.v in the separate Coq 8.19.0
# Islaris environment (nix/arm/islaris.nix).  NOT part of `make prove`.
#   check-islaris.sh ISLARIS_ENV TRACES_DIR
# TRACES_DIR holds the Islaris-generated traces (gen-traces.sh output, or the
# stored copy ports/arm/islaris/instructions/buri_chez_add).  Acceptance is
# decided by coqc.  What it trusts: see the header of buri_chez_add.v.
set -euo pipefail
ENV=$(realpath "$1") T=$(realpath "$2")
here=$(cd "$(dirname "$0")" && pwd)
TIME=${TIME:-/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time}
export PATH="$ENV/bin:$PATH" COQPATH="$ENV/lib/coq/8.19/user-contrib"
coqc --version | grep -q 'version 8.19.0' || { echo 'Need Coq 8.19.0' >&2; exit 1; }
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
mkdir -p "$w/instructions/buri_chez_add" "$w/examples"
cp "$T"/*.v "$w/instructions/buri_chez_add/"
cp "$here/buri_chez_add.v" "$w/examples/"
cd "$w"
Q=(-w -notation-overridden -w -redundant-canonical-projection
   -Q instructions isla.instructions -Q examples isla.examples)
for f in instructions/buri_chez_add/a*.v; do coqc "${Q[@]}" "$f"; done
coqc "${Q[@]}" instructions/buri_chez_add/instrs.v
printf 'Require Import isla.examples.buri_chez_add.\nPrint Assumptions buri_chez_add_fast_path.\n' > examples/audit.v
"$TIME" -v coqc "${Q[@]}" examples/buri_chez_add.v > build.log 2>&1 || { cat build.log >&2; exit 1; }
grep -E 'Elapsed|Maximum resident' build.log
coqc "${Q[@]}" examples/audit.v
echo 'BURI_ISLARIS_CHECK_OK'
