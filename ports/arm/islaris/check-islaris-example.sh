#!/bin/bash
# Reproduce Islaris's own examples/example.v (upstream c978e10f, unmodified,
# with its committed generated traces instructions/example/*.v) in the
# separate Coq 8.19.0 environment of nix/arm/islaris.nix.  This checks that
# the environment is a working Islaris; it is not a Buri result.
#   check-islaris-example.sh ISLARIS_ENV ISLARIS_SRC WORK
set -euo pipefail
ENV=$(realpath "$1") SRC=$(realpath "$2") W=$3
TIME=${TIME:-/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time}
export PATH="$ENV/bin:$PATH"
export COQPATH="$ENV/lib/coq/8.19/user-contrib"
coqc --version | head -1
rm -rf "$W" && mkdir -p "$W/instructions/example" "$W/examples"
cp "$SRC"/instructions/example/*.v "$W/instructions/example/"
cp "$SRC/examples/example.v" "$W/examples/"
cd "$W"
Q=(-w -notation-overridden -w -redundant-canonical-projection
   -Q instructions isla.instructions -Q examples isla.examples)
for f in instructions/example/a*.v; do coqc "${Q[@]}" "$f"; done
coqc "${Q[@]}" instructions/example/instrs.v
"$TIME" -v coqc "${Q[@]}" examples/example.v 2>&1 | grep -E 'Elapsed|Maximum resident|Error|error' || true
test -f examples/example.vo && echo "examples/example.v: checked"
