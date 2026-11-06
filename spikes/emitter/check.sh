#!/bin/bash
# In buri-lps. The gate for route B: binds the proof to the exact bytes of the check build, builds the
# audit, requires the .vo files, replays with rocqchk, and reads the assumptions.
# Exit codes: 2 binary hash, 3 the checker bytes, 4 build or missing .vo, 5 rocqchk, 6 assumptions, 7 Admitted.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s7}; export W; ex=$W/theories/Examples/emitter_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
R=${RUNTIME:-/lps/s7/out/check/runtime}
want=$(cat "$here/check-build.sha256"); got=$(sha256sum "$R" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "BAD_BINARY $got"; exit 2; }
python3 "$here/mkimage.py" "$R" /tmp/s7_chk
export HERE="$here"
python3 - <<'P' || exit 3
import hashlib,os,sys
b=open('/tmp/s7_chk','rb').read(); o=0x36b9c-0x10000; n=0x36d46-0x36b9c
h=hashlib.sha256(b[o:o+n]).hexdigest(); w=open(os.environ['HERE']+'/checker-bytes.sha256').read().strip()
if h!=w: print('BAD_CHECKER_BYTES',h); sys.exit(1)
P
grep -lE '\bAdmitted\b|^Axiom |^Parameter ' "$here"/coq/*.v && { echo FOUND_ADMITTED; exit 7; }
bash "$here/regen.sh" >/dev/null 2>&1
ERRL=6 bash "$here/dbuild.sh" theories/Examples/emitter_ns/MoveAudit.vo || exit 4
cd $W; export OCAMLRUNPARAM=d=4
B=_build/default/theories
for f in MoveContract MoveDecode MoveCompare MoveAudit; do [ -f $B/Examples/emitter_ns/$f.vo ] || { echo MISSING $f; exit 4; }; done
s=$(date +%s); timeout 900 rocqchk -silent -Q _build/default/theories LinuxProcessSemantics $B/Examples/emitter_ns/MoveAudit.vo >/tmp/s7chk.log 2>&1; rc=$?
echo "rocqchk rc=$rc secs=$(( $(date +%s)-s ))"; [ $rc = 0 ] || { tail -3 /tmp/s7chk.log; exit 5; }
# dune replays nothing when up to date, so the audit is compiled again here for its output.
AL=/tmp/s7-audit-$(basename $W).log; export AL
mkdir -p /tmp/s7-audit-$$; rocq compile -Q _build/default/theories LinuxProcessSemantics -o /tmp/s7-audit-$$/MoveAudit.vo $B/Examples/emitter_ns/MoveAudit.v >$AL 2>&1 || { echo AUDIT_FAILED; tail -3 $AL; exit 6; }
python3 - <<'P' || exit 6
import os,re,sys
t=open(os.environ['AL']).read()
names=set(re.findall(r'^\s*([A-Za-z_][\w.]*) :',t,re.M))
ax=set()
for block in re.findall(r'Axioms:\n(.*?)(?=\n(?:Closed under|[A-Za-z_]+ is|File |\Z))',t,re.S):
    ax|=set(re.findall(r'^([A-Za-z_][\w.]*) :',block,re.M))
bad=[a for a in ax if not re.search(r'PrimInt63|PrimString|PrimArray|PrimFloat|functional_extensionality_dep',a) and a.split('.')[-1] not in('int','string','array','get','length','sub','ltb','leb','eqb','land','lor','lsl','lsr','add','mul','lxor','make','set','char63')]
print('assumptions',sorted(a.split('.')[-1] for a in ax)); print('Closed blocks',t.count('Closed under the global context'))
if bad: print('BAD_AXIOMS',bad); sys.exit(1)
if 'Axioms:' not in t and 'Closed under' not in t: print('NO_AUDIT_OUTPUT'); sys.exit(1)
P
echo ALL_OK
