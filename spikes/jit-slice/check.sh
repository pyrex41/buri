#!/bin/bash
# Spike 4 gate. Run in buri-lps. Exits nonzero if any step fails. Steps:
#  1. rerun the capture and require the same bytes the proof names;
#  2. require the helper addresses in the proof to match the capture binary's symbols;
#  3. build the proofs in a private copy of the model tree;
#  4. replay with rocqchk; 5. reject any assumption beyond the permitted primitives.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-/lps/s4/cap}
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
if [ -z "${SKIP_CAPTURE:-}" ]; then
  bash "$here/capture.sh" > /tmp/s4cap.log 2>&1 || { echo "FAIL capture"; tail -5 /tmp/s4cap.log; exit 1; }
fi
want=$(grep -oE 'sha256 [0-9a-f]{64}' "$here/coq/SliceCode.v" | cut -d' ' -f2)
got=$(sha256sum "$OUT/native.bin" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "FAIL bytes: proof names $want, capture is $got"; exit 2; }
echo "ok bytes $got"
for pair in "H_PRIM h_prim" "H_ALLOC h_alloc"; do
  set -- $pair
  addr=$(grep -oE "Definition $1 : word := Z_to_bv 64 0x[0-9a-f]+" "$here/coq/SliceProof.v" | grep -oE '0x[0-9a-f]+$')
  sym=$(awk -v n="$2" '$3==n {print "0x" substr($1, match($1,/[^0]/))}' "$OUT/helpers.txt")
  [ -n "$addr" ] && [ "$addr" = "$sym" ] || { echo "FAIL helper $1: proof $addr, symbol $sym"; exit 3; }
  echo "ok helper $2 $sym"
done
cp "$here"/coq/*.v /work-s4/theories/Examples/jit_slice/
cd /work-s4
s=$(date +%s)
timeout ${T:-1500} dune build theories/Examples/jit_slice -j3 > /tmp/s4build.log 2>&1 || { echo "FAIL build"; grep -vE 'deprecated|^Defined' /tmp/s4build.log | head -20 | cut -c1-240; exit 4; }
echo "ok build $(( $(date +%s)-s ))s"
B=_build/default/theories
s=$(date +%s)
timeout ${T:-1500} rocqchk -silent -Q $B/Examples LinuxProcessSemantics.Examples -Q $B/LinuxProcessSem LinuxProcessSemantics.LinuxProcessSem -Q $B/Riscv LinuxProcessSemantics.Riscv -Q $B/EquivalenceDefinition LinuxProcessSemantics.EquivalenceDefinition -Q $B/Common LinuxProcessSemantics.Common LinuxProcessSemantics.Examples.jit_slice.SliceProof LinuxProcessSemantics.Examples.jit_slice.SliceWitness > /tmp/s4chk.log 2>&1 || { echo "FAIL rocqchk"; tail -5 /tmp/s4chk.log | cut -c1-200; exit 5; }
echo "ok rocqchk $(( $(date +%s)-s ))s"
cat > /tmp/s4a.v <<'V'
From LinuxProcessSemantics.Examples.jit_slice Require Import SliceProof SliceWitness.
Print Assumptions slice_refines.
Print Assumptions w_rel.
V
rocq compile -Q $B/Examples LinuxProcessSemantics.Examples -Q $B/LinuxProcessSem LinuxProcessSemantics.LinuxProcessSem -Q $B/Riscv LinuxProcessSemantics.Riscv -Q $B/EquivalenceDefinition LinuxProcessSemantics.EquivalenceDefinition -Q $B/Common LinuxProcessSemantics.Common /tmp/s4a.v > /tmp/s4a.log 2>&1 || { echo "FAIL audit compile"; tail -5 /tmp/s4a.log | cut -c1-200; exit 6; }
bad=$(grep -E '^[A-Za-z_][A-Za-z0-9_.]* :' /tmp/s4a.log | cut -d' ' -f1 | grep -vE '\.(PrimInt63|PrimString|PrimArray)\.|^functional_extensionality_dep$|PrimInt63|PrimString|PrimArray' | sort -u || true)
[ -z "$bad" ] || { echo "FAIL assumptions: $bad"; exit 6; }
echo "ok assumptions: $(grep -cE '^[A-Za-z_][A-Za-z0-9_.]* :' /tmp/s4a.log) lines, $(grep -c 'Closed under' /tmp/s4a.log) closed"
grep -l Admitted "$here"/coq/*.v && { echo "FAIL Admitted"; exit 7; }
echo ALL_OK
