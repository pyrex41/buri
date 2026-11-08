#!/bin/bash
# Split census, step 1: compile the judge's Rocq dependencies, as scripts/check-shen-jit.sh does
# (Coq -> Stdlib import rename only), into OUT (default /tmp/capture-rocq), for judge_split.sh.
#   judge_split_rocq.sh [OUT]
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
out=${1:-/tmp/capture-rocq}; rm -rf "$out"; mkdir -p "$out"; cd "$out"
for f in Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitLowerStage0; do
  sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/$f.v" > $f.v
  timeout 1800 rocq compile -Q . Buri $f.v > $f.log 2>&1 || { tail -20 $f.log; echo ROCQ_FAILED $f; exit 6; }
done
echo ROCQ_OK
