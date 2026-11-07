#!/bin/bash
# In buri-lps. Spike 9 mutants for the call and kept-register parts: each must fail to build; then the
# unmodified copy must build again.  Builds in /work-s9c, from a copy of this directory in /tmp/s9mut.
here=$(cd "$(dirname "$0")" && pwd); export W=/work-s9c
M=/tmp/s9mut; rm -rf $M; mkdir -p $M; cp -a "$here" $M/spike
T=theories/Examples/emitter_p3_ns/CfAudit.vo
mut() { # name file python-replacement
  local name=$1 file=$2 code=$3
  rm -rf $M/spike/coq-p3; cp -a "$here/coq-p3" $M/spike/coq-p3
  python3 - "$M/spike/coq-p3/$file" "$code" <<'P'
import sys
p, code = sys.argv[1], sys.argv[2]
s = open(p).read()
old, new = code.split('|||')
assert s.count(old) == 1, (p, old, s.count(old))
open(p, 'w').write(s.replace(old, new))
P
  out=$(LIMIT=1800 bash $M/spike/p3-dbuild.sh $T 2>&1)
  if echo "$out" | grep -q '^rc=0'; then echo "MUTANT SURVIVED $name"; else
    echo "rejected $name at $(echo "$out" | grep -m1 -oE 'emitter_p3_ns/[A-Za-z0-9]+\.v' | sed 's|.*/||')"; fi
}
# Bytes (CfCaptured9.v), little-endian at the offsets of the disassembly in RESULTS.md.
B='Definition sn_bytes : list Z := ['
mut b-ret-misaligned CfCaptured9.v "147; 128; 160; 1; 35; 48; 20; 2|||147; 128; 192; 1; 35; 48; 20; 2"
mut b-window-wrong CfCaptured9.v "19; 4; 4; 2; 5; 70|||19; 4; 132; 1; 5; 70"
mut b-kept-wrong-reg CfCaptured9.v "1; 20; 42; 138; 35; 60|||1; 20; 170; 138; 35; 60"
mut b-argcount-wrong CfCaptured9.v "5; 70; 3; 179|||9; 70; 3; 179"
# Certificate.
mut c-kept-claimed CfCaptured9.v "Some (mkS None 15 0 0 (Some 3) None)|||Some (mkS None 15 0 0 (Some 3) (Some 3))"
mut c-arg-not-current CfCaptured9.v "Some (mkS (Some 6) 71 0 0 None None)|||Some (mkS (Some 6) 7 0 0 None None)"
# Checker definition (CfDefs.v): weakened, each must break a soundness proof.
mut s-no-fp-at-call CfDefs.v "same (yA y 8) (Lin KFp (8 * a)) && same (yA y 9)|||same (yA y 9)"
mut s-no-args-current CfDefs.v "forallb (fun j => Z.testbit (sM s) (a + 2 + j)) (nats n) &&|||"
mut s-frame-not-kept-at-call CfDefs.v "frame_kept_call s a y &&|||"
mut s-kept-not-checked CfDefs.v "reg_post d v y 20 (sK0 t) && |||"
mut s-kept-not-restored CfDefs.v "&& reg_post None Unk y 20 (sK0 s) &&|||&&"
mut s-callee-not-proc CfDefs.v "match ckinds c k with Some (KPtr _ t) => Z.eqb t 5 | _ => false end &&|||"
echo "== clean"
rm -rf $M/spike/coq-p3; cp -a "$here/coq-p3" $M/spike/coq-p3
LIMIT=1800 bash $M/spike/p3-dbuild.sh $T | head -2
