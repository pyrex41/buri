#!/bin/bash
# Each gate in scripts/check-shen-jit.sh must fire. Run in the buri-lps container.
root=$(cd "$(dirname "$0")/../.." && pwd)
# GATE_DIR: scratch directory (removed at the end); DIFF_OUT: a finished lane run with the differential.
m=${GATE_DIR:-/tmp/p1mut}; diffout=${DIFF_OUT:-/tmp/p1}; gl=$m.log; expect() { # name wanted-exit command...
  name=$1; want=$2; shift 2; "$@" > $gl 2>&1; rc=$?
  if [ "$rc" = "$want" ]; then echo "fired $name (exit $rc): $(grep -E 'NOT_THE|DRIFT|AUDIT_MIS|DIFFERENTIAL_CHANGED|ROCQ_FAILED|STAGE0_' $gl | head -1 | cut -c1-80)"
  else echo "DID_NOT_FIRE $name wanted $want got $rc"; missed=1; tail -5 $gl | cut -c1-200; fi; }
fresh() { rm -rf $m; mkdir -p $m/root; cd "$root"; tar cf - --exclude spikes --exclude .git --exclude _build . | tar xf - -C $m/root; chmod -R u+w $m/root; mkdir -p $m/root/spikes; }
fresh; expect wrong-binary 3 env SHEN_JIT_BIN=/lps/runtime bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i 's/("hd",PHd,1)/("hd",PHd,2)/' $m/root/rocq/JitBytecode.v; expect table-drift 4 bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i "s|sed 's/^From Coq Require/From Stdlib Require/'|sed -e 's/^From Coq Require/From Stdlib Require/' -e 's/Definition next /Definition next_x /'|" $m/root/scripts/check-shen-jit.sh; expect spec-drift 5 env JIT_OUT=$m/o bash $m/root/scripts/check-shen-jit.sh
fresh; echo 19 > $m/root/rocq/audit.d/Audit_Jit.count; expect audit-count 7 env JIT_OUT=$m/o SKIP_DIFF=1 bash $m/root/scripts/check-shen-jit.sh
# Since Phase 2, JitLowerPrim.p_hd rejects the hd mutant (exit 6) before the differential; the rounding mutant still exercises exit 10.
fresh; sed -i 's/| PHd, \[v\] => match v with VPair a _ => ret a/| PHd, [v] => match v with VPair _ a => ret a/' $m/root/rocq/JitBytecode.v; expect model-mutant-hd 6 env JIT_OUT=$m/o bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i 's/let up := if Z.ltb half rest then true/let up := if Z.ltb half rest then false/' $m/root/rocq/JitFloat.v; expect model-mutant-rounding 10 env JIT_OUT=$m/o bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i '/^ev 437 /d' $m/root/tests/shen-jit/known-differences.txt; expect known-list-missing 1 env JIT_OUT=$diffout python3 $m/root/tests/shen-jit/compare_known.py $m/root/tests/shen-jit/known-differences.txt ev ops ct
fresh; echo 'ev 0 | diff-ok | invented' >> $m/root/tests/shen-jit/known-differences.txt; expect known-list-stale 1 env JIT_OUT=$diffout python3 $m/root/tests/shen-jit/compare_known.py $m/root/tests/shen-jit/known-differences.txt ev ops ct
fresh; sed -i 's/Some (Z.compare (i \* den) (if neg then - n else n))/compare (of_Z i) b/' $m/root/rocq/JitBytecode.v; expect model-rounded-compare 6 env JIT_OUT=$m/o SKIP_DIFF=1 bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i 's/^core 6 57 0$/core 7 56 0/' $m/root/tests/shen-jit/stage0-accepted.txt; expect stage0-count-changed 12 env JIT_OUT=$m/o SKIP_DIFF=1 bash $m/root/scripts/check-shen-jit.sh
fresh; sed -i 's/| B.IMove d. s. :: r. => if N.eqb d d. \&\& N.eqb s s. then Some r. else None/| B.IMove d0 s0 :: r0 => if N.eqb d d0 then Some r0 else None/' $m/root/rocq/JitLowerCheck.v; expect checker-unsound 6 env JIT_OUT=$m/o SKIP_DIFF=1 bash $m/root/scripts/check-shen-jit.sh
# The cons chain's parameter-slot guard follows lower.shen; dropping it stays sound (no proof fails) but rejects writer's chain into a parameter slot.
fresh; sed -i 's/ if N.leb (2 + B.code_arity c) d then match p, args with/ if true then match p, args with/' $m/root/rocq/JitLowerCheck.v; expect chain-guard-dropped 12 env JIT_OUT=$m/o SKIP_DIFF=1 bash $m/root/scripts/check-shen-jit.sh
rm -rf $m
echo GATE_TESTS_DONE
exit ${missed:-0}
