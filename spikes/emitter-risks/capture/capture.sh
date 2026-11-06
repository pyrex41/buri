#!/bin/bash
# In buri-lps. usage: capture.sh NAME ARITY. Extracts the defun from stage 0, runs the real JIT, disassembles.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); SJ=/lps/s8/sj; OUT=/lps/s8/cap; mkdir -p $OUT; cd $SJ
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
cp "$here/capture.c" tests/capture8.c
OBJS="build/heap.o build/objects.o build/image.o build/prims.o build/reader.o build/loader.o build/jit.o build/dict.o build/profile.o build/thread.o build/ffi.o build/win32.o build/sljitLir.o"
cc-rv64 -std=c11 -O2 -g -DSLJIT_DEBUG=0 -DSLJIT_VERBOSE=0 -include spikes-overlay/arena.h \
  -o $OUT/capture tests/capture8.c $OBJS spikes-overlay/arena.o ${EXTRA_OBJ:-} -static -lm -ldl -lpthread -Wl,-T,spikes-overlay/arena.lds
grep -h "^(defun $1 " build/stage0/*.sbc > $OUT/$1.sbc
cat $OUT/$1.sbc | cut -c1-400
qemu-riscv64 $OUT/capture $OUT/$1.sbc $1 $OUT/$1.bin $2 | tee $OUT/$1.log
riscv64-linux-gnu-objdump -D -b binary -mriscv:rv64 --adjust-vma=0 $OUT/$1.bin > $OUT/$1.dis
