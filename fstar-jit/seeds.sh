#!/bin/sh
# Rerun the modules holding the three hardest lemmas with --z3seed 1..5, one run at a time (nice'd).
cd "$(dirname "$0")"
out=seeds.txt; : > $out
for m in JitMeta JitLowerCheck JitLowerEquiv; do
  for s in 1 2 3 4 5; do
    ./check.sh Buri.$m.fst --z3seed $s 2>/dev/null | tail -1 | tee -a $out
  done
done
