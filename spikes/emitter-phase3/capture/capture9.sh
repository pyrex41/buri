#!/bin/bash
# In buri-lps. usage: capture9.sh NAME ARITY [EXTRA_DEFUNS...]. Spike 9: spike 8's capture harness on the 0.4 tree
# (/tmp/s9/sj, last built by build.sh check). Extracts the defun (and any callees named) from stage 0, runs the real
# JIT, disassembles. Output /tmp/s9/cap/NAME.{sbc,bin,log,dis}; with EXTRA_OBJ=spikes-overlay/spike9.o the checker
# runs and SPIKE_DUMP=NAME writes its certificate dump.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); SJ=/tmp/s9/sj; OUT=/tmp/s9/cap; mkdir -p $OUT; cd $SJ
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
cp "$here/capture.c" tests/capture9.c
OBJS="build/heap.o build/objects.o build/image.o build/prims.o build/reader.o build/loader.o build/jit.o build/dict.o build/profile.o build/thread.o build/ffi.o build/win32.o build/sljitLir.o"
cc-rv64 -std=c11 -O2 -g -DSLJIT_DEBUG=0 -DSLJIT_VERBOSE=0 -include spikes-overlay/arena.h \
  -o $OUT/capture tests/capture9.c $OBJS spikes-overlay/arena.o ${EXTRA_OBJ:-} -static -lm -ldl -lpthread -Wl,-T,spikes-overlay/arena.lds
n=$1; a=$2; shift 2
: > $OUT/$n.sbc
for f in "$@" "$n"; do grep -h "^(defun $f " build/stage0/*.sbc >> $OUT/$n.sbc; done
cut -c1-300 $OUT/$n.sbc
qemu-riscv64 $OUT/capture $OUT/$n.sbc $n $OUT/$n.bin $a | tee $OUT/$n.log
riscv64-linux-gnu-objdump -D -b binary -mriscv:rv64 --adjust-vma=0 $OUT/$n.bin > $OUT/$n.dis
sha256sum $OUT/capture $OUT/$n.bin
