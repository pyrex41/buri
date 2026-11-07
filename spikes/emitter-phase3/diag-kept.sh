#!/bin/bash
# In buri-lps. Diagnostic for the checkbad-kept question: rebuilds check and checkbad-kept with a checker whose
# SPIKE_DUMP appends (so every function named NAME is dumped, not only the last), dumps every in-domain
# accepted stage-1 function, and compares bytes between the builds, masking the h_alloc call (whose address
# differs between the two binaries). Restores the normal check build afterwards.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); T=/tmp/s9/sj; Q=/tmp/s9q; mkdir -p $Q
sed 's/fopen(getenv("SPIKE_DUMP_OUT") ? getenv("SPIKE_DUMP_OUT") : "\/tmp\/spike-dump.txt", "w")/fopen(getenv("SPIKE_DUMP_OUT") ? getenv("SPIKE_DUMP_OUT") : "\/tmp\/spike-dump.txt", "a")/' \
  "$here/overlay/check_fn.c" > $Q/check_fn_append.c
grep -q '"a")' $Q/check_fn_append.c
for v in check checkbad-kept; do
  rm -rf $Q/sp-$v; mkdir -p $Q/sp-$v/overlay; cp -a "$here"/*.sh "$here"/*.py $Q/sp-$v/; cp $Q/check_fn_append.c $Q/sp-$v/overlay/check_fn.c
  bash $Q/sp-$v/build.sh $v >/dev/null
  cp /tmp/s9/out/$v/runtime $Q/rt-$v
  rm -rf $Q/st && cp -r $T/build/stage0 $Q/st
  for n in lambda 'boolean?'; do
    rm -f "$Q/$v-$n.dump"
    ( cd $Q && SPIKE_DUMP="$n" SPIKE_DUMP_OUT="$Q/$v-$n.dump" qemu-riscv64 $Q/rt-$v --stage1 st $Q/img-$v >/dev/null 2>&1 )
  done
done
python3 - $Q <<'P'
import sys, subprocess
Q=sys.argv[1]
def recs(path):
    out=[]; cur={}
    for l in open(path):
        k,_,v=l.partition(' ')
        if k=='base' and cur: out.append(cur); cur={}
        cur[k]=v.split()
    if cur: out.append(cur)
    return out
def dis(b):
    open(Q+'/t.bin','wb').write(bytes(b))
    d=subprocess.run(['riscv64-linux-gnu-objdump','-D','-b','binary','-mriscv:rv64',Q+'/t.bin'],capture_output=True,text=True).stdout
    ins=[l.split('\t',2)[-1] for l in d.splitlines() if l.startswith('  ') and ':' in l]
    return ['jal <helper>' if i.startswith('jal\t') else i for i in ins]
for n in ['lambda','boolean?']:
    a=recs(f'{Q}/check-{n}.dump'); b=recs(f'{Q}/checkbad-kept-{n}.dump')
    print(n, 'dumped', len(a), len(b))
    for i,(x,y) in enumerate(zip(a,b)):
        dx=dis([int(t) for t in x['bytes']]); dy=dis([int(t) for t in y['bytes']])
        uses=any(('s4' in t or 's5' in t) for t in dx)
        print(f'  #{i} words-equal={x["words"]==y["words"]} code-equal-mod-helper={dx==dy} touches-s4/s5={uses} kept-in-states={any(s.split(":")[5:]!=["-1","-1"] for s in x["states"])}')
P
bash "$here/build.sh" check >/dev/null && sha256sum /tmp/s9/out/check/runtime | cut -c1-16
