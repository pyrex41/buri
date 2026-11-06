#!/bin/bash
# In buri-lps. usage: build.sh base|check|checkbad-slot|checkbad-tag|checkbad-store. Output /lps/s8/out/<v>/{runtime,shen-jit}.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); v=$1; T=/lps/s8/sj; cd $T
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
cp /lps/s8/jit.c.base src/runtime/jit.c
sed -i '/spike8/d' local.mk
if [ "$v" != base ]; then
  python3 "$here/apply_hook.py" src/runtime/jit.c
  cat >> src/runtime/jit.c <<'C'
C
  python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a='static void *compile_code(VM *vm, V code)\n{'
b='''static const char *symbol_cstr_spike(VM *vm, V name)
{
    (void)vm;
    if (!is_symbol(name)) return NULL;
    static char buf[128];
    V str = ptr(name)[SYM_NAME];
    size_t n = string_length(str) < 127 ? string_length(str) : 127;
    memcpy(buf, string_bytes(str), n);
    buf[n] = 0;
    return buf;
}

'''+a
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
  case $v in
  checkbad-slot) python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a="sljit_emit_op1(c, SLJIT_MOV, SLJIT_MEM1(SLJIT_S3), sizeof(V), OPND(e, arg[1]));"
b="sljit_emit_op1(c, SLJIT_MOV, SLJIT_MEM1(SLJIT_S3), sizeof(V), OPND(e, arg[0]));"
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
  ;;
  checkbad-store) python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a="""    if (!(dead_store(e, dst) || consumed_next(e, dst)))
        sljit_emit_op1(e->c, SLJIT_MOV, HOME(e, dst), CACHE);"""
b="""    /* wrong: never stores */"""
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
  ;;
  checkbad-room) python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a="sljit_emit_op2(c, SLJIT_ADD, R1, HP, IMM(n * sizeof(V)));"
b="sljit_emit_op2(c, SLJIT_ADD, R1, HP, IMM((n - 2) * sizeof(V)));"
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
  ;;
  esac
  TAGS=$(python3 - <<'P'
import re
s=open('src/runtime/value.h').read()
print(' '.join('-DSPIKE_TAG_%s=%s'%(n,re.search(r'TAG_%s\s*=\s*(\d+)'%n,s).group(1)) for n in ['OBJECT','PAIR','PROC','SYMBOL']))
P
)
  cc-rv64 -std=c11 -O2 -g $TAGS -D_DEFAULT_SOURCE -c "$here/overlay/check_fn.c" -o spikes-overlay/spike8.o
  echo 'LDLIBS += spikes-overlay/spike8.o # spike8' >> local.mk
fi
touch src/runtime/jit.c src/runtime/main.c
rm -f build/runtime build/shen-jit build/shen-jit.img build/jit.o
make -j3 build/runtime CC=cc-rv64 >/lps/s8/make-$v.log 2>&1 || { grep -E 'error|Error' /lps/s8/make-$v.log | head -20 | cut -c1-170; exit 1; }
out=/lps/s8/out/$v; mkdir -p $out; cp build/runtime $out/
( cd build; SPIKE_STATS=1 qemu-riscv64 ./runtime --stage1 stage0 shen-jit.img 2> $out/stage1.err; rc=$?; grep spike-check $out/stage1.err | head -12; [ $rc = 0 ] || { echo "stage 1 failed: $(grep -v spike-check $out/stage1.err | head -2)"; exit 9; }
  cat runtime shen-jit.img > shen-jit; chmod +x shen-jit; cp runtime shen-jit $out/ )
sha256sum $out/runtime $out/shen-jit | cut -c1-16,65-
cp /lps/s8/jit.c.base src/runtime/jit.c
