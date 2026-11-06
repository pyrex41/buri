#!/bin/bash
# In buri-lps. Route A's rungs: build, require the .vo files, replay with rocqchk, print assumptions, and
# reject two spec mutants. Exit 4 build, 5 rocqchk, 6 assumptions, 8 a mutant was accepted.
here=$(cd "$(dirname "$0")" && pwd); W=/work-s7; ex=$W/theories/Examples/emitter_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null; export OCAMLRUNPARAM=d=4
A="theories/Examples/emitter_ns/EmitKind.vo theories/Examples/emitter_ns/EmitPush.vo"
ERRL=3 bash "$here/dbuild-a.sh" $A || exit 4
cd $W; B=_build/default/theories; D=$B/Examples/emitter_ns
for f in EmitKind EmitPush; do s=$(date +%s); timeout 600 rocqchk -silent -Q _build/default/theories LinuxProcessSemantics $D/$f.vo >/tmp/s7a.log 2>&1 || { echo ROCQCHK_FAIL $f; exit 5; }; echo "rocqchk $f ok secs=$(( $(date +%s)-s ))"; done
mkdir -p /tmp/s7aa; cat > /tmp/s7aa/AAudit.v <<'V'
From LinuxProcessSemantics.Examples.emitter_ns Require Import EmitKind EmitPush.
Print Assumptions operand_kind_slot.
Print Assumptions push_inst16_fast.
V
rocq compile -Q _build/default/theories LinuxProcessSemantics /tmp/s7aa/AAudit.v > /tmp/s7aa/a.log 2>&1 || { echo AUDIT_FAIL; exit 6; }
grep -E '^(Closed|Axioms|[A-Za-z_.]+ :)' /tmp/s7aa/a.log | sed -E 's/ :.*//; s/.*\.//' | sort -u | tr '\n' ' '; echo
if grep -E '^[A-Za-z_.]+ :' /tmp/s7aa/a.log | grep -vE 'Prim(Int63|String|Array)|^(int|string|array|get|length|sub|ltb|leb|eqb|land|lor|lsl|lsr) :' | grep -q .; then echo BAD_AXIOMS; exit 6; fi
cp "$here"/coq-a/EmitKind.v /tmp/s7aa/EK.bak; cp "$here"/coq-a/EmitPush.v /tmp/s7aa/EP.bak
mut() { sed -i "$2" "$ex/$3"; cmp -s "$ex/$3" "$here/coq-a/$3" && { echo NOT_APPLIED $1; return; }
  timeout 300 dune build theories/Examples/emitter_ns/${3%.v}.vo -j3 >/tmp/s7am.log 2>&1 && [ -f $B/Examples/emitter_ns/${3%.v}.vo ] && { echo "MUTANT_ACCEPTED $1"; rc=8; } || echo "rejected $1: $(grep -m1 Error /tmp/s7am.log | cut -c1-60)"
  cp "$here/coq-a/$3" "$ex/$3"; }
rc=0
mut kind-frame 's/else 151\./else 150./' EmitKind.v
mut wrong-halfword 's/(w2 (W ins))\./(w2 (W (ins + 1)))./' EmitPush.v
ERRL=2 bash "$here/dbuild-a.sh" $A >/dev/null || { echo RESTORE_FAILED; exit 4; }
echo A_DONE; exit $rc
