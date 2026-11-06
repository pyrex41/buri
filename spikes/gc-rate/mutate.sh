#!/bin/bash
# In buri-lps. Each mutant must fail to compile. The unmodified proofs must compile first and
# last; any other outcome is reported loudly.
here=$(cd "$(dirname "$0")" && pwd); W=/work-s5; ex=$W/theories/Examples/gc_rate_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
T=theories/Examples/gc_rate_ns/GcAudit.vo
build() { cp "$1"/coq/*.v "$ex"/; (cd $W && timeout ${LIMIT:-900} dune build $T -j3 >/tmp/mut.log 2>&1); }
bash "$here/regen.sh"; build "$here" && echo "baseline-ok" || { echo BASELINE_FAILED; grep -m3 Error /tmp/mut.log; exit 1; }
spec() { # name file sed
  m=$(mktemp -d); cp -a "$here/coq" "$m/"; sed -i "$3" "$m/coq/$2"
  cmp -s "$m/coq/$2" "$here/coq/$2" && { echo "MUTANT_NOT_APPLIED $1"; return; }
  if build "$m"; then echo "MUTANT_ACCEPTED $1"; else echo "rejected spec $1: $(grep -m1 -E 'Error' /tmp/mut.log | cut -c1-70) $(grep -m1 -oE 'File "[^"]*", line [0-9]+' /tmp/mut.log | sed 's/.*gc_rate_ns.//')"; fi
  rm -rf "$m"
}
byte() { # name addr:hex; a patch that leaves the bytes unchanged is reported, not tested
  python3 - "$2" <<'P' || { echo "MUTANT_NOT_APPLIED $1"; return; }
import sys
va,h=sys.argv[1].split(':'); b=open('/lps/runtime','rb').read(); o=int(va,16)-0x10000
sys.exit(0 if b[o:o+len(bytes.fromhex(h))]!=bytes.fromhex(h) else 1)
P
  bash "$here/regen.sh" "$2"
  if build "$here"; then echo "MUTANT_ACCEPTED $1"; else echo "rejected bytes $1: $(grep -m1 -E 'Error' /tmp/mut.log | cut -c1-70) $(grep -m1 -oE 'File "[^"]*", line [0-9]+' /tmp/mut.log | sed 's/.*gc_rate_ns.//')"; fi
  bash "$here/regen.sh"
}
spec code-words Rung1ObjWords.v 's/else if t =? 8 then 10/else if t =? 8 then 11/'
spec header-type-shift Rung1ObjWords.v 's/Z.shiftr h 3) mod 32/Z.shiftr h 4) mod 32/'
spec forward-marker Rung2Paths.v 's/Definition V_FORWARD : word := Z_to_bv 64 34/Definition V_FORWARD : word := Z_to_bv 64 35/'
spec nonptr-tag-list Rung2Paths.v 's#(t = 0 \\/ t = 2 \\/ t = 4 \\/ t = 7)%Z#(t = 0 \\/ t = 1 \\/ t = 2 \\/ t = 4 \\/ t = 7)%Z#'
spec spine-write-order Rung2Spine.v 's/(wbytes m cur (w8 w0)) cq (w8 w1)/(wbytes m cur (w8 w1)) cq (w8 w0)/'
spec pair-moved-tag Rung2Spine.v 's/v_or (Z_to_bv 64 3) q/v_or (Z_to_bv 64 1) q/'
spec object-next-offset Rung2Spine.v 's/(at_off c 16) (w8 (at_off q (8 \* n))))/(at_off c 16) (w8 (at_off q (8 * n + 8))))/'
spec saved-reg-order Rung2Frame.v 's/(at_off fp 32) (w8 s0)) (at_off fp 24) (w8 s1)/(at_off fp 32) (w8 s1)) (at_off fp 24) (w8 s0)/'
spec scan-skips-slot Rung3Scan.v 's/slot (0x1198c : word) (Z_to_bv 64 2) m1 (at_off s 8) a1 m2\./m2 = m1./'
spec inv-show-unscanned Rung4Graph.v 's/if (bv_unsigned x <? bv_unsigned a) then img phi w else w/if (bv_unsigned x <? bv_unsigned a) then w else w/'
spec iso-drops-tail Rung4Graph.v 's/| reach_tail : forall p, reach r p -> tag (o1 p) = 3 -> reach r (ptr_of (o1 p))\./| reach_tail : forall p, reach r p -> reach r (ptr_of (o1 p))./'
byte ow-jump-table 45e50:00000000
byte ow-li-3 14e26:1145
byte cv-forward-marker 11c04:13061002
byte cv-wrong-cursor 11d4c:b3875200
byte cv-loop-step 11d3e:c107
byte scan-wrong-slot 1198c:233ca400
build "$here" && echo "restored-ok" || echo RESTORE_FAILED
