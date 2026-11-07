#!/bin/bash
# In buri-lps. Each mutant patches the proof image's bytes (bin-gen.py ADDR:HEX), regenerates the fetch facts,
# and must make the named proof fail to build. Then the unmodified image is regenerated and must build again.
# A rejected mutant only shows this proof script fails on it.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s9a}; export W; ex=$W/theories/Examples/s9bin_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
R=/tmp/s9/frozen/check-runtime
run() { # name patch target
  python3 "$here/bin-gen.py" $R "$ex" "$2" >/dev/null || { echo "$1 MUTANT_NOT_APPLIED"; return; }
  out=$(LIMIT=${LIMIT:-2400} bash "$here/bin-dbuild.sh" "$3" 2>&1)
  if echo "$out" | grep -q '^rc=0'; then echo "$1 MUTANT_ACCEPTED"; else
    echo "$1 rejected: $(echo "$out" | grep -m1 '^File' | sed 's/.*s9bin_ns\///')"; fi
}
T=theories/Examples/s9bin_ns
# decode, compressed path: rd' extraction mask 31 -> 15 (andi a7,a1,31 at 0x3e9d4)
run d-rd-mask 3e9d4:93f8f500 $T/DecContract.vo
# run_block, sd case: the record's value k stored at 520 instead of 528 (sd s11,528(a1) at 0x3da92)
run r-store-offset 3da92:23b4b521 $T/RbContract.vo
# run_block, sd case: the store-count limit 16 -> 15 (li a1,16 at 0x3da58)
run r-store-limit 3da58:bd45 $T/RbContract.vo
python3 "$here/bin-gen.py" $R "$ex" >/dev/null
out=$(LIMIT=${LIMIT:-2400} bash "$here/bin-dbuild.sh" $T/DecContract.vo $T/RbContract.vo 2>&1)
echo "$out" | grep -q '^rc=0' && echo "baseline rebuilt OK" || { echo "BASELINE FAILED"; echo "$out" | head -5; exit 1; }
