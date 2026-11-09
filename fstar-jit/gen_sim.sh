#!/bin/sh
# Buri.JitLowerSim.fst is generated from Buri.JitLowerSim.fst.tpl (constructor-pattern shorthands).
cd "$(dirname "$0")" && python3 -I expand_patterns.py Buri.JitLowerSim.fst.tpl Buri.JitLowerSim.fst \
  Buri.JitLowerKont.fst Buri.JitLowerRel.fst Buri.JitLowerStep.fst
