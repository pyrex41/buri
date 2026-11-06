#!/bin/bash
# In buri-lps. Fetches Shen/JIT 0.3, applies spike 2's arena patch, builds stage 0, and prepares /work-s8.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
COMMIT=b4ccf2dff97031ee624692bb32d2addd18cacb39
T=/lps/s8/sj; mkdir -p /lps/s8
[ -d /work-s8 ] || cp -a /work /work-s8
[ -d $T ] || git clone -q https://github.com/tizoc/shen-jit.git $T
cd $T; git config --global --add safe.directory '*'; git checkout -q $COMMIT; git status --short | head -3
# Spike 2's patch, minus its heap.c hunk, which 0.3 moved; the same one-line change is made by sed.
git checkout -q -- . ; rm -rf spikes-overlay local.mk
git apply --exclude=src/runtime/heap.c "$here/../riscv-build/shen-jit-rv64-arena.patch"
sed -i 's|^#ifdef MADV_HUGEPAGE$|#if defined(MADV_HUGEPAGE) \&\& !defined(SPIKE_NO_THP)|' src/runtime/heap.c
grep -c 'SPIKE_NO_THP' src/runtime/heap.c
# 0.3 no longer compiles for RISC-V: emit_sqrt has only arm64 and x86-64 arms. It serves hand-written
# native code, which the claim excludes. fsqrt.d rd, rs, for RV64.
python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a='#else\n#error "no square root for this target"'
b='#elif (defined SLJIT_CONFIG_RISCV_64 && SLJIT_CONFIG_RISCV_64)\n    sljit_u32 fsqrt = 0x5A007053u | rs << 15 | rd << 7;\n    sljit_emit_op_custom(c, &fsqrt, sizeof fsqrt);\n#else\n#error "no square root for this target"'
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
make deps >/dev/null
make build/stage0/.done >/dev/null
( cd build && grep ' stage0/' ../generated.sha256 | sha256sum -c --quiet - )
echo "stage 0 matches generated.sha256"
cp src/runtime/jit.c /lps/s8/jit.c.base
cc-rv64 -std=c11 -O2 -g -c spikes-overlay/arena.c -o spikes-overlay/arena.o
make -j3 build/runtime CC=cc-rv64 >/lps/s8/make-base.log 2>&1 || { tail -20 /lps/s8/make-base.log; exit 1; }
( cd build; qemu-riscv64 ./runtime --stage1 stage0 shen-jit.img; cat runtime shen-jit.img > shen-jit; chmod +x shen-jit; sha256sum runtime shen-jit )
