#!/bin/bash
# Spike 3: compile Buri's KLambda semantics, unedited except for the rewrites below,
# under the Rocq that Theorem's model needs. Run in the buri-lps container.
# The tree is generated: the only copy of the spec stays in rocq/.
set -uo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:-/tmp/rocq9-port}
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
rm -rf "$out"; mkdir -p "$out"
FILES=${FILES:-"Lambda Observation KLSyntax KLValue KLSemantics KLMetatheory KLWellFormed KLTail KLBridge KLExamples"}
for f in $FILES; do
  sed -f "$root/spikes/rocq9-port/rewrites.sed" "$root/rocq/$f.v" > "$out/$f.v"
done
# Gate: the generated copy may differ from rocq/ only on Stdlib import lines.
for f in $FILES; do
  d=$(diff "$root/rocq/$f.v" "$out/$f.v" || true)   # diff exits 1 when files differ
  other=$(printf '%s\n' "$d" | grep -E '^[<>]' | grep -vE '^[<>] From (Coq|Stdlib) Require' || true)
  if [ -n "$other" ]; then
    echo "SPEC_DRIFT $f"; exit 2
  fi
  echo "same-except-imports $f $(printf '%s\n' "$d" | grep -c '^>' || true)"
done
cd "$out"; rc=0
for f in $FILES; do
  s=$(date +%s)
  if rocq compile -Q . Buri "$f.v" > "$f.log" 2>&1; then echo "ok $f $(( $(date +%s)-s ))s"
  else echo "FAIL $f"; grep -v 'deprecated' "$f.log" | head -${ERRLINES:-14} | cut -c1-220; rc=1; break; fi
done
[ $rc = 0 ] || exit $rc
# Independent replay, then link against Theorem's model in one Rocq session.
rocqchk -silent -Q . Buri $(for f in $FILES; do echo "Buri.$f"; done) > chk.log 2>&1; echo "rocqchk_rc=$?"; tail -2 chk.log | cut -c1-200
cat > Assumptions.v <<'V'
From Buri Require Import Observation KLMetatheory KLWellFormed KLTail KLBridge.
Print Assumptions Observation.refinement_preserves_errors_res.
Print Assumptions Observation.terminates_unique.
Print Assumptions KLMetatheory.progress.
Print Assumptions KLMetatheory.step_deterministic.
V
rocq compile -Q . Buri Assumptions.v 2>&1 | grep -vE 'deprecated|^$' | cut -c1-160 | head -24
B=/work/_build/default/theories
cat > Link.v <<'V'
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_source Proof.
Check Observation.refines_res.
Check KLSemantics.step.
Check source_wexit.
Check omni_strong_universal.
V
rocq compile -Q . Buri -Q $B/Examples LinuxProcessSemantics.Examples -Q $B/LinuxProcessSem LinuxProcessSemantics.LinuxProcessSem -Q $B/Riscv LinuxProcessSemantics.Riscv -Q $B/EquivalenceDefinition LinuxProcessSemantics.EquivalenceDefinition -Q $B/Common LinuxProcessSemantics.Common Link.v > link.log 2>&1; echo "link_rc=$?"; grep -vE 'deprecated|^Defined' link.log | cut -c1-150 | head -24
grep -hc . *.log >/dev/null; echo "deprecation_warnings=$(cat *.log | grep -c deprecated)"; cat *.log | grep -oE '\[[a-z-]+,deprecated[^]]*\]' | sort | uniq -c | sort -rn | head -5
exit 0
