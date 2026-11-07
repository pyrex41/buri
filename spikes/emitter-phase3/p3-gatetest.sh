#!/bin/bash
# In buri-lps. Shows each gate of p3-check.sh fires, from a modified copy of this directory in /tmp/s9gt,
# building in /work-s9c. Prints one line per case: name, exit code, the gate's message.
here=$(cd "$(dirname "$0")" && pwd); export W=/work-s9c
G=/tmp/s9gt
fresh() { rm -rf $G; mkdir -p $G; cp -a "$here" $G/spike; }
run() { # name [env...]
  local name=$1; shift
  out=$(env "$@" bash $G/spike/p3-check.sh 2>&1); rc=$?
  echo "$name | $rc | $(echo "$out" | grep -E '^(FAIL|ALL_OK)' | head -1)"
}
fresh; run clean-before
fresh; printf 'x' > /tmp/s9gt-fakebin; run wrong-capture-binary CAPTURE_BIN=/tmp/s9gt-fakebin
fresh; sed -i 's/Definition sn_cuts : list Z := \[18;/Definition sn_cuts : list Z := [20;/' $G/spike/coq-p3/CfCaptured9.v
run instance-edited-by-hand
fresh; python3 - $G/spike/capture/data9/shortnatters.bin <<'P'
import sys; p=sys.argv[1]; b=bytearray(open(p,'rb').read()); b[0x12]^=1; open(p,'wb').write(b)
P
python3 $G/spike/capture/gen_instance9.py $G/spike/capture/data9/shortnatters.raw $G/spike/capture/data9/shortnatters.bin \
  $G/spike/capture/data9/shortnatters.cert $G/spike/coq-p3/CfCaptured9.v >/dev/null
run dump-bytes-changed-instance-regenerated
fresh; python3 - $G/spike/coq-p3/CfCall.v <<'P'
import sys; p=sys.argv[1]; s=open(p).read()
a="split; [apply wrap_mod4; exact Hmod|]."
assert s.count(a)==1; open(p,'w').write(s.replace(a,"split; [exact Hmod|]."))
P
run ill-typed-proof-step
fresh; run rocqchk-missing-file VO=/work-s9c/_build/default/theories/Examples/emitter_p3_ns/NoSuch.vo
fresh; cat >> $G/spike/coq-p3/CfAudit.v <<'C'
From Stdlib Require Import Classical.
Lemma gt_uses_classic : forall P : Prop, P \/ ~ P. Proof. exact classic. Qed.
Print Assumptions gt_uses_classic.
C
run extra-axiom-in-audit
fresh; python3 - $G/spike/coq-p3/CfCall.v <<'P'
import sys; p=sys.argv[1]; s=open(p).read()
a="Lemma nats_in"
open(p,'w').write(s.replace(a,"Lemma gt_admitted : 1 = 2.\nAdmitted.\n\nLemma nats_in",1))
P
run admitted-in-source
fresh; run clean-after
rm -rf $G /tmp/s9gt-fakebin
