#!/bin/sh
# Wave-D primitives-lane mutants (tests/mutate-prims2.py): a changed pinned
# definition or an unjustified restatement must be refused by Rocq.
# Called by scripts/proof-mutations; ROCQ_DIR overrides the compiled tree.
set -eu
cd "$(dirname "$0")/.."
dir=${ROCQ_DIR:-_build/rocq}
for name in $(python3 tests/mutate-prims2.py); do
  if scripts/rocq coqc -Q "$dir" Buri "_build/mutations/$name.v" > "_build/mutations/$name.log" 2>&1; then
    echo "Mutant incorrectly accepted: $name" >&2; exit 1
  fi
  grep -Eq 'Killed|Out of memory' "_build/mutations/$name.log" && { echo "Resource exhausted (not a rejection): $name" >&2; exit 2; }
  grep -q '^Error' "_build/mutations/$name.log" || { cat "_build/mutations/$name.log"; exit 1; }
  printf 'Rejected proof mutation: %s\n' "$name"
done
