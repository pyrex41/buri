#!/bin/bash
# Spike gate, in the style of scripts/check-arm.sh. Run inside the spike's
# aarch64 container, with /root/env from env.nix.
#   1. builds program.S and binds every w_* line of BuriJitWords.v to its bytes
#   2. compiles Búri's reused modules and the spike's theorems
#   3. audits Print Assumptions
#   4. requires one-bit mutants of the two generated words to be rejected
#   5. replays the compiled proofs with coqchk
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
export PATH=/root/env/bin:$PATH COQPATH=/root/env/lib/coq/8.19/user-contrib
ulimit -s unlimited; ulimit -v 9000000
W=${W:-/work3}; mkdir -p "$W"; cd "$W"
cp "$ROOT"/ports/arm/coq/BuriArm{Adds,Decode,Seq,FastPath}.v .
cp "$HERE"/BuriJit{Words,Models,Mem}.v .
Q=(-R /root/env/lib/coq/8.19/user-contrib/SailArm SailArm -Q . BuriArm)

gcc -static -nostdlib -nostartfiles -no-pie -Wl,-T,"$HERE/../rwx.lds" -Wl,--no-warn-rwx-segments -Wl,--build-id=none -o prog "$HERE/../program.S"
sha256sum prog
python3 - prog <<'P'
import re,struct,subprocess,sys
o=subprocess.run(['objdump','-d',sys.argv[1]],capture_output=True,text=True).stdout
words=[int(m,16) for m in re.findall(r'^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s',o,re.M)]
# The generated words, from the movz/movk pair that writes each one.
def movzk(z,k): return ((z>>5)&0xffff)|(((k>>5)&0xffff)<<16)
pairs=[(words[i],words[i+1]) for i in range(len(words)-1) if words[i]>>21==0x294 and words[i+1]>>21==0x395]
gen=[movzk(*p) for p in pairs]
want={'w_mov':gen[0],'w_ret':gen[1],'w_str':words[3],'w_blr':next(w for w in words if (w&0xfffffc1f)==0xd63f0000),
      'w_isb':next(w for w in words if w==0xd5033fdf),'w_dsb':next(w for w in words if w==0xd5033b9f),
      'w_ic':next(w for w in words if (w&0xffffffe0)==0xd50b7520),'w_dc':next(w for w in words if (w&0xffffffe0)==0xd50b7b20)}
s=open('BuriJitWords.v').read()
for k,v in want.items():
    m=re.search(r'Definition %s\s*: mword 32 := Ox"([0-9A-F]{8})"'%k,s)
    if not m or int(m.group(1),16)!=v: sys.exit(f'{k}: theorem word differs from program bytes {v:08X}')
    print(f'  bound {k} = {v:08X}')
P
for f in BuriArmAdds BuriArmDecode BuriArmSeq BuriArmFastPath BuriJitWords BuriJitModels BuriJitMem; do
  [ "$f.vo" -nt "$f.v" ] || coqc "${Q[@]}" "$f.v" > "$f.log" 2>&1 || { tail -5 "$f.log"; exit 1; }
done
python3 - <<'P'
import re,sys
allowed={'ClassicalDedekindReals.sig_not_dec','ClassicalDedekindReals.sig_forall_dec','FunctionalExtensionality.functional_extensionality_dep'}
n=0
for f in ['BuriJitWords','BuriJitModels','BuriJitMem']:
    t=open(f+'.log').read()
    for b in re.split(r'\n(?=Axioms:|Closed under the global context)',t):
        n+=b.startswith('Closed') or b.startswith('Axioms:')
        if b.startswith('Axioms:'):
            names=set(re.findall(r'^([A-Za-z_][\w.]*) :',b,re.M))
            if names-allowed: sys.exit(f'{f}: unexpected axioms {names-allowed}')
print(f'  audited {n} Print Assumptions blocks: only the three Coq-stdlib axioms of __DecodeA64')
P
mutant() { # word, replacement, theorem head to cut before
  python3 - "$1" "$2" "$3" <<'P'
import sys
a,b,cut=sys.argv[1:]
s=open('BuriJitWords.v').read().replace('Ox"%s"'%a,'Ox"%s"'%b)
open('BuriJitMutant.v','w').write(s[:s.index(cut)])
P
  if coqc "${Q[@]}" BuriJitMutant.v > mut.log 2>&1; then echo "Incorrectly admitted mutant $2" >&2; exit 1; fi
  grep -q 'Unable to unify\|Tactic failure\|No matching clauses' mut.log || { tail -5 mut.log >&2; echo "mutant $2 failed for another reason" >&2; exit 1; }
  echo "  rejected $1 -> $2"
}
mutant 52800540 52800541 'Theorem ret_decode'       # mov w1,#42
mutant D65F03C0 D65F03C1 'Theorem str_decode'       # a one-bit change in ret's Rm field
coqchk -silent -o "${Q[@]}" BuriArm.BuriJitWords BuriArm.BuriJitModels BuriArm.BuriJitMem > chk.log 2>&1
grep -A30 'Axioms' chk.log | head -24
echo CHECK_OK
