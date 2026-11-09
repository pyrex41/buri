#!/bin/sh
# Buri.JitLowerSim.fst and Buri.JitLowerSimEval.fst are generated from their .fst.tpl files:
# constructor-pattern shorthands are expanded with arities read from the declarations.
cd "$(dirname "$0")" || exit 1
for m in JitLowerSim JitLowerSimEval; do
  python3 -I expand_patterns.py Buri.$m.fst.tpl Buri.$m.fst Buri.JitLowerKont.fst Buri.JitLowerRel.fst Buri.JitLowerStep.fst || exit 1
done
