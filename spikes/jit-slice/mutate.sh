#!/bin/bash
# Spike 4 negative tests. Run in buri-lps. Each mutant changes bytes and, where named, the
# decode table to match, so it reaches the refinement proof instead of failing at the table.
# A rejection only shows this proof script does not go through for that mutant.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
CAP=${OUT:-/lps/s4/cap}/native.bin
run() { # name, python snippet editing bytes "d" (bytearray) or empty, sed on table, sed on spec
  name=$1; py=$2; tbl=$3; spec=$4; prf=${5:-}
  t=$(mktemp -d); cp "$here"/coq/*.v "$t"/
  python3 - "$CAP" "$t/m.bin" <<P
import sys
d=bytearray(open(sys.argv[1],'rb').read())
$py
open(sys.argv[2],'wb').write(d)
P
  python3 "$here/gen_capture.py" "$t/m.bin" 5c140 "$t/SliceCode.v" >/dev/null
  if [ -n "$tbl" ]; then sed "$tbl" "$here/gen_facts.py" > "$t/gf.py"; else cp "$here/gen_facts.py" "$t/gf.py"; fi
  python3 "$t/gf.py" "$t/SliceFacts.v"
  [ -z "$spec" ] || sed -i "$spec" "$t/SliceBytecode.v"
  [ -z "$prf" ] || sed -i "$prf" "$t/SliceProof.v"
  rm -f "$t/m.bin" "$t/gf.py"
  if [ -z "$py$tbl$spec$prf" ]; then :; fi
  cp "$t"/*.v /work-s4/theories/Examples/jit_slice/
  cd /work-s4
  if timeout 900 dune build theories/Examples/jit_slice/SliceProof.vo -j3 > /tmp/s4m.log 2>&1; then
    echo "MUTANT_ACCEPTED $name"; status=1
  else
    w=$(grep -m1 -E '^File ' /tmp/s4m.log | sed -E 's/.*jit_slice\/([A-Za-z]+\.v)", line ([0-9]+).*/\1:\2/')
    echo "rejected $name at $w: $(grep -m1 -E '^Error' -A1 /tmp/s4m.log | tr '\n' ' ' | cut -c1-90)"
  fi
  rm -rf "$t"
}
status=0
# Control: an unchanged tree must build, or a rejection below means nothing.
run control-unchanged "" "" ""
[ "$status" = 1 ] && { echo "control built, as it must"; status=0; } || { echo "CONTROL_FAILED"; exit 9; }
# A changed emitted word: the tail is read from slot 2, not slot 3 (ld ra,24(s0) to ld ra,16(s0)).
run word-reads-wrong-slot "d[0x2c]=0x04" "s/42 Load SZ8 true 1 8 24/42 Load SZ8 true 1 8 16/" ""
# The same change with the table left alone: rejected at the decode fact.
run word-table-unchanged "d[0x2c]=0x04" "" ""
# A wrong value tag in the code: the result is tagged 4, not TAG_PAIR 3.
run result-tag-wrong "d[0x34]=0x49" "s/50 OpImm ALU_ADD 10 19 3/50 OpImm ALU_ADD 10 19 4/" ""
# A wrong tag in the test: x - 5 instead of x - 3 (TAG_PROC, not TAG_PAIR).
run tag-test-wrong "d[0x8]=0xb9" "s/6 OpImm ALU_ADD 11 18 4093/6 OpImm ALU_ADD 11 18 4091/" ""
# The spec's tag is wrong, and the code is right.
run spec-tag-wrong "" "" "s/Definition TAG_PAIR : Z := 3%Z/Definition TAG_PAIR : Z := 5%Z/"
# Success and failure swapped at the tag test (bnez to beqz).
run tag-branch-swapped "d[0xf]=0x8a" "s/14 Branch BC_NE 5 0 52/14 Branch BC_EQ 5 0 52/" ""
# Success and failure swapped at the heap limit (bltu to bgeu).
run limit-branch-swapped "d[0x23]=0x77" "s/34 Branch BC_LTU 6 11 78/34 Branch BC_GEU 6 11 78/" ""
# Success and failure swapped in the spec, with the code right.
run spec-branch-swapped "" "" "s/if Z.eqb (tag3 x) TAG_PAIR then/if negb (Z.eqb (tag3 x) TAG_PAIR) then/"
# The allocator is told the wrong size, with the table to match.
run alloc-wrong-words "d[0x7a]=0x91" "s/122 OpImm ALU_ADD 11 0 2|2/122 OpImm ALU_ADD 11 0 4|2/" ""
# Restore and require the unchanged proof still builds.
cp "$here"/coq/*.v /work-s4/theories/Examples/jit_slice/
cd /work-s4; timeout 900 dune build theories/Examples/jit_slice/SliceProof.vo -j3 >/dev/null 2>&1 && echo restored-ok || { echo RESTORE_FAILED; exit 8; }
exit $status
