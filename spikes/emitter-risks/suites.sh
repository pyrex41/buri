#!/bin/bash
# In buri-lps. usage: suites.sh VARIANT. Contract, kernel and extension suites under qemu-riscv64, with the checker's counts.
v=$1; B=/lps/s8/out/$v/shen-jit; T=/lps/s8/sj; K=$T/.deps/kernel; cd $T
export SPIKE_STATS=1
w=/tmp/s8w-$v; mkdir -p $w; printf '#!/bin/sh\nexec qemu-riscv64 %s "$@"\n' "$B" > $w/sj; chmod +x $w/sj
run() { local s=$(date +%s%N); "$@"; local rc=$?; echo "ms=$(( ($(date +%s%N)-s)/1000000 )) rc=$rc"; }
echo "== contract"; run bash -c "timeout 1800 $w/sj script contract/examples.shen 2>&1 | grep -E 'passed|failed|spike-check|^[0-9]+/' | tail -40"
echo "== kernel"; ( cd $K/tests && run bash -c "yes y | head -200 | timeout 3000 $w/sj script runme.shen 2>&1 | grep -A1 -E '^passed \.\.\.|spike-check' | grep -vE '^--' | tail -40" )
echo "== extensions"; ( cd $K && run bash -c "timeout 1800 $w/sj script tests/extensions/runme.shen < /dev/null 2>&1 | grep -A1 -E '^passed \.\.\.|spike-check' | grep -vE '^--' | tail -40" )
