#!/bin/sh
# Port-fix lane mutants (tests/mutate-portfix.py): an unpatched capture or a
# restated theorem must be refused by Rocq. Called by scripts/proof-mutations.
set -eu
cd "$(dirname "$0")/.."
for name in $(python3 tests/mutate-portfix.py); do
  if scripts/rocq coqc -Q _build/rocq Buri "_build/mutations/$name.v" > "_build/mutations/$name.log" 2>&1; then
    echo "Mutant incorrectly accepted: $name" >&2; exit 1
  fi
  grep -Eq 'Killed|Out of memory' "_build/mutations/$name.log" && { echo "Resource exhausted (not a rejection): $name" >&2; exit 2; }
  grep -q '^Error' "_build/mutations/$name.log" || { cat "_build/mutations/$name.log"; exit 1; }
  printf 'Rejected proof mutation: %s\n' "$name"
done
