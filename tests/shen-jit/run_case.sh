#!/bin/bash
# One differential set, in the buri-lps container: run_case.sh NAME FILE KIND [GLOBALS]
# Writes /tmp/p1/d/NAME.out: one verdict per captured case, computed by Rocq.
set -u
name=$1; file=$2; kind=$3
here=$(cd "$(dirname "$0")" && pwd)
base=${JIT_OUT:-/tmp/p1}; d=$base/d; mkdir -p "$d"; cd "$d"
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
cat > run_$name.shen <<S
(load "$here/capture.shen")
(sj.cap.$kind-file "$file")
S
timeout 600 qemu-riscv64 "${SJ_BIN:-/lps/p2/sj/build/shen-jit}" script run_$name.shen > cap_$name.txt 2> cap_$name.err
echo "capture_rc=$?"
python3 $here/gen_diff.py cap_$name.txt "${STAGE0:-/lps/p2/sj/build/stage0}" Gen_$name.v
sed -i 's/^From Coq Require/From Stdlib Require/' Gen_$name.v
s=$(date +%s); timeout 900 rocq compile -Q $base Buri -Q . JitDiff Gen_$name.v > gen_$name.log 2>&1; echo "gen_rc=$? $(( $(date +%s)-s ))s"; grep -m3 -A6 'Error' gen_$name.log | cut -c1-200
cat > Run_$name.v <<S
From Stdlib Require Import List String.
From Buri Require Import JitBytecode.
From JitDiff Require Import JitDiffLib Gen_$name.
Import ListNotations JitBytecode.JitBytecode JitDiffLib.JitDiffLib.
Definition out :=
  let pt := prim_tree in
  let m0 := set_gvals (with_std (seal_names (sealing_off (preload pt (sealing_on empty_machine) defs)) sealed_names)) globals in
  map verdict_text (run_all pt m0 cases).
Eval vm_compute in out.
S
s=$(date +%s); timeout ${RUNT:-1500} rocq compile -Q $base Buri -Q . JitDiff Run_$name.v > $name.out 2>&1; echo "run_rc=$? $(( $(date +%s)-s ))s"; test -s $name.out && wc -c $name.out
