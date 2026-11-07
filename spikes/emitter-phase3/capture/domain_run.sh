#!/bin/bash
# In buri-lps. For one build variant, compiles each in-domain stage 0 function through the real JIT with
# the checker linked, and prints accept/reject per function. usage: domain_run.sh VARIANT
v=$1; here=$(cd "$(dirname "$0")" && pwd)
bash "$here/../build.sh" $v > /lps/s8/domain-build-$v.log 2>&1
cd /lps/s8/sj; export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
OBJS="build/heap.o build/objects.o build/image.o build/prims.o build/reader.o build/loader.o build/jit.o build/dict.o build/profile.o build/thread.o build/ffi.o build/win32.o build/sljitLir.o"
cp "$here/capture.c" tests/capture8.c
cc-rv64 -std=c11 -O2 -g -DSLJIT_DEBUG=0 -DSLJIT_VERBOSE=0 -include spikes-overlay/arena.h \
  -o /lps/s8/cap/capture-$v tests/capture8.c $OBJS spikes-overlay/arena.o spikes-overlay/spike8.o -static -lm -ldl -lpthread -Wl,-T,spikes-overlay/arena.lds
cp /lps/s8/jit.c.base src/runtime/jit.c
acc=0; rej=0
while read -r name arity n; do
  grep -h "^(defun $name " build/stage0/*.sbc > /tmp/d8.sbc
  out=$(SPIKE_STATS=1 timeout 60 qemu-riscv64 /lps/s8/cap/capture-$v /tmp/d8.sbc "$name" /tmp/d8.bin $arity 2>&1)
  r=$(echo "$out" | grep -m1 "spike-check: functions" ); why=$(echo "$out" | grep -m1 "reason" | sed 's/spike-check: reason 1 //')
  case "$r" in *accepted=1*) acc=$((acc+1)); echo "accept $name";; *rejected=1*) rej=$((rej+1)); echo "reject $name: $why";; *) echo "none $name: $(echo "$out" | tail -1 | cut -c1-80)";; esac
done < /lps/s8/domain.txt
echo "TOTAL $v accepted=$acc rejected=$rej"
