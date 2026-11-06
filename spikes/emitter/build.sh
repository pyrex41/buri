#!/bin/bash
# In buri-lps. Usage: build.sh base|census|check. Output: /lps/s7/out/<variant>/{runtime,shen-jit}.
# Starts from spike 2's tree at /lps/s7/sj (715bf60 plus the arena patch); never edits ~/projects/shen-jit.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); v=$1; T=/lps/s7/sj; cd $T
cp /lps/s7/jit.c.base src/runtime/jit.c
sed -i '/spike7/d' local.mk
obj=""
case $v in
  base) ;;
  census|census-check) python3 "$here/apply_hook.py" src/runtime/jit.c; src=census.c ;;
  check) python3 "$here/apply_hook.py" src/runtime/jit.c; src=check_move.c ;;
  checkbad) # Gate test only: the emitter reads the wrong slot for a move, so the checker must stop it.
    python3 "$here/apply_hook.py" src/runtime/jit.c
    python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a="""                sljit_emit_op1(c, SLJIT_MOV, R0, OPND(&e, p[2]));
                store_result(&e, p[1]);"""
b="""                sljit_emit_op1(c, SLJIT_MOV, R0, OPND(&e, p[2] + 1));
                store_result(&e, p[1]);"""
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
    src=check_move.c ;;
esac
if [ "$v" != base ]; then
  cc-rv64 -std=c11 -O2 -g -c "$here/overlay/$src" -o spikes-overlay/spike7.o
  cat >> local.mk <<'L'
LDLIBS += spikes-overlay/spike7.o # spike7
L
fi
touch src/runtime/jit.c src/runtime/main.c
rm -f build/runtime build/shen-jit build/shen-jit.img build/jit.o
make -j3 build/runtime CC=cc-rv64 >/lps/s7/make-$v.log 2>&1 || { tail -20 /lps/s7/make-$v.log; exit 1; }
out=/lps/s7/out/$v; mkdir -p $out
( cd build; qemu-riscv64 ./runtime --stage1 stage0 shen-jit.img; cat runtime shen-jit.img > shen-jit; chmod +x shen-jit; cp runtime shen-jit shen-jit.img $out/ )
sha256sum $out/runtime $out/shen-jit | cut -c1-16,65-
cp /lps/s7/jit.c.base src/runtime/jit.c
