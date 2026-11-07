#!/bin/bash
# In buri-lps. usage: build.sh base|stats|check|check-nokept|checkbad-kept
#   base         the 0.4 tree as pinned (port patch only), built in /tmp/s9/sj
#   stats        base plus emitter counters for the kept registers (no checker; counters change no emitted code)
#   check        spike 8's checker with kept-register support, plus the counters
#   check-nokept the same checker with the kept registers treated as unknown (spike 8's behavior)
#   checkbad-kept check, with an emitter bug: a slow path's go-back reloads the wrong slot into a kept register
# Output /tmp/s9/out/<v>/{runtime,shen-jit}. The tree is a copy of /lps/p4/sj (d3348ce + ports/shen-jit patch),
# so hashes differ from the named binary's: -g records the build directory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); v=$1; T=/tmp/s9/sj; cd $T
export ZIG_GLOBAL_CACHE_DIR=/tmp/zg ZIG_LOCAL_CACHE_DIR=/tmp/zl
[ -f /tmp/s9/jit.c.base ] || cp src/runtime/jit.c /tmp/s9/jit.c.base
cp /tmp/s9/jit.c.base src/runtime/jit.c
sed -i '/spike9/d' local.mk
if [ "$v" != base ]; then
  python3 "$here/stats_hook.py" src/runtime/jit.c
fi
case $v in check|check-nokept|checkbad-kept)
  python3 "$here/apply_hook.py" src/runtime/jit.c
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
  if [ "$v" = checkbad-kept ]; then python3 - <<'P'
p='src/runtime/jit.c'; s=open(p).read()
a="""            sljit_emit_op1(e->c, SLJIT_MOV, KEPT_REG(k), 0, SLOT(s->kept[k]));
        }
    sljit_set_label(sljit_emit_jump(e->c, SLJIT_JUMP), s->back);"""
b="""            sljit_emit_op1(e->c, SLJIT_MOV, KEPT_REG(k), 0, SLOT(s->kept[k] + 1)); /* wrong slot */
        }
    sljit_set_label(sljit_emit_jump(e->c, SLJIT_JUMP), s->back);"""
assert s.count(a)==1; open(p,'w').write(s.replace(a,b))
P
  fi
  TAGS=$(python3 - <<'P'
import re
s=open('src/runtime/value.h').read()
print(' '.join('-DSPIKE_TAG_%s=%s'%(n,re.search(r'TAG_%s\s*=\s*(\d+)'%n,s).group(1)) for n in ['OBJECT','PAIR','PROC','SYMBOL']))
P
)
  extra=; [ "$v" = check-nokept ] && extra=-DSPIKE_NO_KEPT
  cc-rv64 -std=c11 -O2 -g $TAGS $extra -D_DEFAULT_SOURCE -c "$here/overlay/check_fn.c" -o spikes-overlay/spike9.o
  echo 'LDLIBS += spikes-overlay/spike9.o # spike9' >> local.mk
  ;;
esac
touch src/runtime/jit.c src/runtime/main.c
rm -f build/runtime build/shen-jit build/shen-jit.img build/jit.o
make -j4 build/runtime CC=cc-rv64 >/tmp/s9/make-$v.log 2>&1 || { grep -E 'error|Error' /tmp/s9/make-$v.log | head -20 | cut -c1-170; exit 1; }
out=/tmp/s9/out/$v; mkdir -p $out; cp build/runtime $out/
cp src/runtime/jit.c $out/jit.c
( cd build; SPIKE_STATS=1 qemu-riscv64 ./runtime --stage1 stage0 shen-jit.img 2> $out/stage1.err; rc=$?; { grep -E 'spike-(check|kept)' $out/stage1.err | head -14 || true; }; [ $rc = 0 ] || { echo "stage 1 failed: $(grep -v spike- $out/stage1.err | head -2)"; exit 9; }
  cat runtime shen-jit.img > shen-jit; chmod +x shen-jit; cp runtime shen-jit shen-jit.img $out/ )
sha256sum $out/runtime $out/shen-jit | cut -c1-16,65-
cp /tmp/s9/jit.c.base src/runtime/jit.c
