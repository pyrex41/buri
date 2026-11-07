#!/bin/bash
# In buri-lps. usage: suites.sh VARIANT [TAG]. Contract, kernel and extension suites under qemu-riscv64, with the
# checker's and the kept-register counters. Output goes to stdout; run twice to check the counts repeat.
v=$1; B=/tmp/s9/out/$v/shen-jit; T=/tmp/s9/sj; K=$T/.deps/kernel; cd $T
export SPIKE_STATS=1
w=/tmp/s9w-$v; mkdir -p $w; printf '#!/bin/sh\nexec qemu-riscv64 %s "$@"\n' "$B" > $w/sj; chmod +x $w/sj
echo "binary $(sha256sum $B | cut -c1-64)"
run() { local s=$(date +%s%N); "$@"; local rc=$?; echo "ms=$(( ($(date +%s%N)-s)/1000000 )) rc=$rc"; }
echo "== contract"; run bash -c "timeout 1800 $w/sj script contract/examples.shen 2>&1 | grep -E 'passed|failed|spike-|^[0-9]+/' | tail -40"
echo "== kernel"; ( cd $K/tests && run bash -c "yes y | head -200 | timeout 3000 $w/sj script runme.shen 2>&1 | grep -A1 -E '^passed \.\.\.|spike-' | grep -vE '^--' | tail -40" )
echo "== extensions"; ( cd $K && run bash -c "timeout 1800 $w/sj script tests/extensions/runme.shen < /dev/null 2>&1 | grep -A1 -E '^passed \.\.\.|spike-' | grep -vE '^--' | tail -40" )
