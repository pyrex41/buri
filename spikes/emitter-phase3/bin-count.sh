#!/bin/bash
# In buri-lps. Instruction counts for the C checker's decode and run_block in the frozen runtime, and
# everything run_block reaches. Usage: bin-count.sh [RUNTIME]
# Counts are of instructions objdump prints between a symbol and the next one (nm -S size), excluding
# nothing: these functions have no padding nops inside their ranges (checked below).
set -euo pipefail
R=${1:-/tmp/s9/frozen/check-runtime}
want=99300f3221ec53511d023f408e11ee6bd3b89f375ce36253d48a38a5a842955e
got=$(sha256sum "$R" | cut -d' ' -f1)
[ "$got" = "$want" ] || echo "NOTE runtime is not the frozen build: $got"
nmo=$(riscv64-linux-gnu-nm -S "$R")
count() { # name -> "addr size count calls"
  local l a s
  l=$(echo "$nmo" | awk -v n="$1" '$4==n {print $1, $2}')
  a=$((16#${l%% *})); s=$((16#${l##* }))
  objdump_out=$(riscv64-linux-gnu-objdump -d --no-show-raw-insn --start-address=$a --stop-address=$((a+s)) "$R")
  n=$(echo "$objdump_out" | grep -cE '^ +[0-9a-f]+:')
  nops=$(echo "$objdump_out" | grep -cE '^ +[0-9a-f]+:\s+nop$' || true)
  calls=$(echo "$objdump_out" | grep -oE '(jalr|jal|call)\s.*<[A-Za-z_.0-9]+>' | grep -oE '<[A-Za-z_0-9]+>' | sort | uniq -c | tr -s ' ' | tr '\n' ' ' || true)
  jt=$(echo "$objdump_out" | grep -cE '\sjr\s+a[0-9]$' || true)
  printf '%-10s 0x%x size 0x%x  %4d instructions  nops %d  indirect-jr %d  calls: %s\n' "$1" $a $s $n $nops $jt "${calls:-none}"
}
count decode
count run_block
count memcpy
echo "inlined into decode: dec16, dec32 (no symbols):"; echo "$nmo" | grep -wE 'dec16|dec32' || echo "  none present"
echo "inlined into run_block: load, setr, add_k, lin, same (no symbols):"; echo "$nmo" | grep -wE 'load|setr|add_k|lin|same' || echo "  none present"
