#!/bin/bash
# Opt-in check of ports/arm/islaris/buri_chez_add_shen.v (E2E-21) in the
# separate Coq 8.19.0 Islaris environment (nix/arm/islaris.nix).  NOT part of
# `make prove`.
#   check-islaris-shen.sh ISLARIS_ENV TRACES_DIR
# Compiles rocq/ChezLayout.v and rocq/ChezWord.v (the same files scripts/prove
# compiles with Coq 8.18) under logical path Buri, the traces, buri_chez_add.v
# and buri_chez_add_shen.v, then audits the assumptions.  Acceptance is decided
# by coqc; this script only stages files.
set -euo pipefail
ENV=$(realpath "$1") T=$(realpath "$2")
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
export PATH="$ENV/bin:$PATH" COQPATH="$ENV/lib/coq/8.19/user-contrib"
coqc --version | grep -q 'version 8.19.0' || { echo 'Need Coq 8.19.0' >&2; exit 1; }
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
mkdir -p "$w/instructions/buri_chez_add" "$w/examples" "$w/repr"
cp "$T"/*.v "$w/instructions/buri_chez_add/"
cp "$here/buri_chez_add.v" "$here/buri_chez_add_shen.v" "$w/examples/"
cp "$root/rocq/ChezLayout.v" "$root/rocq/ChezWord.v" "$w/repr/"
cd "$w"
Q=(-w -notation-overridden -w -redundant-canonical-projection -w -deprecated
   -Q instructions isla.instructions -Q examples isla.examples -Q repr Buri)
coqc "${Q[@]}" repr/ChezLayout.v
coqc "${Q[@]}" repr/ChezWord.v
for f in instructions/buri_chez_add/a*.v; do coqc "${Q[@]}" "$f"; done
coqc "${Q[@]}" instructions/buri_chez_add/instrs.v
coqc "${Q[@]}" examples/buri_chez_add.v
coqc "${Q[@]}" examples/buri_chez_add_shen.v
printf 'Require Import isla.examples.buri_chez_add_shen.\nPrint Assumptions buri_chez_add_shen.\nPrint Assumptions fxw_no_overflow_iff.\n' > examples/audit.v
coqc "${Q[@]}" examples/audit.v | tee audit.log
[ "$(grep -c '^Closed under the global context$' audit.log)" = 2 ] || { echo 'unexpected assumptions' >&2; exit 1; }
echo 'BURI_ISLARIS_SHEN_CHECK_OK'
