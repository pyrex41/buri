#!/bin/bash
# Opt-in Shen/JIT lane gate (E2E-37). NOT part of `make prove`, whose 8.18 run compiles the
# same rocq/Jit*.v sources. This run needs the Rocq in toolchain.lock.json's shen_jit entry
# and qemu-riscv64, so it runs in the container from spikes/jit-in-model/setup.sh.
#
#   SHEN_JIT_SRC  checkout of the pinned Shen/JIT, with build/stage0 (default /lps/s4/sj)
#   SHEN_JIT_BIN  the named binary (default /lps/shen-jit)
#
# Acceptance of theorems is decided by rocq and rocqchk. The differential part compares
# samples with the binary: agreement is test evidence, never proof. Passing does not
# verify Shen/JIT.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
src=${SHEN_JIT_SRC:-/lps/s4/sj}
bin=${SHEN_JIT_BIN:-/lps/shen-jit}
out=${JIT_OUT:-/tmp/p1}; export JIT_OUT="$out"
want=$(python3 -c "import json;print(json.load(open('$root/toolchain.lock.json'))['shen_jit']['binary_sha256'])")
got=$(sha256sum "$bin" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "NOT_THE_NAMED_BINARY $got"; exit 3; }
python3 "$root/tests/shen-jit/check_tables.py" "$root" "$src" || exit 4
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$out"; cd "$out"
FILES="Observation KLSyntax KLValue JitFloat JitBytecode JitMeta JitProfile Audit_Jit"
for f in $FILES; do
  sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/$f.v" > "$f.v"
  d=$(diff "$root/rocq/$f.v" "$f.v" || true)   # diff exits 1 when the files differ
  other=$(printf '%s\n' "$d" | grep -E '^[<>]' | grep -vE '^[<>] From (Coq|Stdlib) Require' || true)
  [ -z "$other" ] || { echo "SPEC_DRIFT $f"; exit 5; }
  rm -f "$f.vo"
  rocq compile -Q . Buri "$f.v" > "$f.log" 2>&1 || { tail -20 "$f.log"; echo "ROCQ_FAILED $f"; exit 6; }
  [ -s "$f.vo" ] || { echo "NO_OUTPUT $f"; exit 6; }
done
expected=$(cat "$root/rocq/audit.d/Audit_Jit.count")
closed=$(grep -c '^Closed under the global context$' Audit_Jit.log || true)
[ "$closed" = "$expected" ] || { cat Audit_Jit.log; echo "AUDIT_MISMATCH $closed of $expected"; exit 7; }
rocqchk -silent -Q . Buri $(for f in $FILES; do echo "Buri.$f"; done) > chk.log 2>&1 || { tail -5 chk.log; echo "ROCQCHK_FAILED"; exit 8; }
echo "rocq-9: ${closed} audited statements closed, rocqchk passed"
if [ -n "${SKIP_DIFF:-}" ]; then echo "differential: NOT RUN (SKIP_DIFF set)"; exit 0; fi
d="$out/d"; mkdir -p "$d"; cd "$d"
cat "$src/tests/kl/ops.kl" "$root/tests/shen-jit/ops-calls.kl" > ops-all.kl
sed 's/^From Coq Require/From Stdlib Require/' "$root/tests/shen-jit/JitDiffLib.v" > JitDiffLib.v
rm -f JitDiffLib.vo; rocq compile -Q "$out" Buri -Q . JitDiff JitDiffLib.v > lib.log 2>&1 || { tail lib.log; exit 9; }
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ev "$src/tests/kl/eval-cases.kl" kl > log_ev.txt 2>&1 &
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ops "$d/ops-all.kl" kl > log_ops.txt 2>&1 &
SJ_BIN=$bin STAGE0=$src/build/stage0 bash "$root/tests/shen-jit/run_case.sh" ct "$src/contract/examples.shen" contract > log_ct.txt 2>&1 &
wait
python3 "$root/tests/shen-jit/compare_known.py" "$root/tests/shen-jit/known-differences.txt" ev ops ct || { echo "DIFFERENTIAL_CHANGED"; exit 10; }
echo "BURI_SHEN_JIT_LANE_OK (not a verification of Shen/JIT)"
