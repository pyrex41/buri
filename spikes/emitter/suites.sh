#!/bin/bash
# In buri-lps. Usage: suites.sh VARIANT. Runs contract, kernel and extension suites under qemu-riscv64.
v=$1; B=/lps/s7/out/$v/shen-jit; T=/lps/s7/sj; cd $T
K=$T/.deps/kernel
run() { local s=$(date +%s%N); "$@"; local rc=$?; echo "ms=$(( ($(date +%s%N)-s)/1000000 )) rc=$rc"; }
w=/tmp/s7w-$v; mkdir -p $w; printf '#!/bin/sh\nexec qemu-riscv64 %s "$@"\n' "$B" > $w/sj; chmod +x $w/sj
echo "== contract"; run bash -c "timeout 1800 $w/sj script contract/examples.shen 2>&1 | tail -1"
echo "== kernel"; ( cd $K/tests && run bash -c "yes y | head -200 | timeout 3000 $w/sj script runme.shen 2>&1 | grep -A1 '^passed \.\.\.' | tail -2" )
echo "== extensions"; ( cd $K && run bash -c "timeout 1800 $w/sj script tests/extensions/runme.shen < /dev/null 2>&1 | grep -A1 '^passed \.\.\.' | tail -2" )
