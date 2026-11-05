#!/bin/bash
# Runs in buri-lps. Builds the capture harness against the spike 2 arena objects and
# disassembles what the JIT emitted. Output in $OUT.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
SJ=/lps/s4/sj; OUT=${OUT:-/lps/s4/cap}; mkdir -p "$OUT"
ZIG=zig-linux-aarch64-0.13.0
if [ ! -x /opt/$ZIG/zig ]; then
  curl -fsSL -o /opt/zig.tar.xz https://ziglang.org/download/0.13.0/$ZIG.tar.xz
  echo "041ac42323837eb5624068acd8b00cd5777dac4cf91179e8dad7a7e90dd0c556  /opt/zig.tar.xz" | sha256sum -c -
  tar -C /opt -xf /opt/zig.tar.xz
fi
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
cd "$SJ"
cp "$here/capture.c" tests/capture_slice.c
OBJS="build/heap.o build/objects.o build/image.o build/prims.o build/reader.o build/loader.o build/jit.o build/dict.o build/profile.o build/thread.o build/ffi.o build/win32.o build/sljitLir.o"
/opt/$ZIG/zig cc -target riscv64-linux-musl -mcpu=baseline_rv64 -fno-sanitize=undefined -fno-pie -no-pie \
  -std=c11 -O2 -g -DSLJIT_DEBUG=0 -DSLJIT_VERBOSE=0 -include spikes-overlay/arena.h \
  -o "$OUT/capture" tests/capture_slice.c $OBJS spikes-overlay/arena.o -static -lm -ldl -lpthread -Wl,-T,spikes-overlay/arena.lds
cp "$here/slice.sbc" "$OUT/slice.sbc"
qemu-riscv64 "$OUT/capture" "$OUT/slice.sbc" "$OUT/native.bin" | tee "$OUT/capture.log"
riscv64-linux-gnu-objdump -D -b binary -mriscv:rv64 --adjust-vma=0 "$OUT/native.bin" > "$OUT/native.dis"
riscv64-linux-gnu-nm "$OUT/capture" | grep -E " (h_prim|h_alloc)$" | tee "$OUT/helpers.txt"
sha256sum "$OUT/capture" "$OUT/native.bin"
