#!/bin/sh
# Verify every module from an empty cache, one module at a time (nice'd), in dependency order;
# then the stage 0 judge (run_stage0.sh). Writes timings-all.txt.
cd "$(dirname "$0")"
rm -rf _cache; mkdir -p _cache
out=timings-all.txt; : > $out
t0=$(date +%s)
for m in Lib LibTest Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitFloatTest JitBytecode JitMeta \
         JitProfile JitLowerRel JitLowerCheck JitLowerStage0 JitLowerKont JitLowerStable JitLowerPrim \
         JitLowerStep JitLowerThm JitLowerEquiv Unfinished; do
  ./check.sh Buri.$m.fst 2>/dev/null | tail -1 | tee -a $out
done
echo "modules total wall $(( $(date +%s) - t0 ))s" | tee -a $out
