#!/bin/bash
# In buri-lps. The gate for spike 8: binds the theorem to the captured bytes and the binary that made them,
# builds every statement, requires the .vo files, replays with rocqchk, and reads the assumptions.
# Exit codes: 2 capture binary hash, 3 generated instance differs from the dump, 4 build or missing .vo,
#             5 rocqchk, 6 assumptions, 7 Admitted or an axiom in the sources, 0 ALL_OK.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s8}; export W
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
BIN=${CAPTURE_BIN:-/lps/s8/cap/capture}
[ "$(sha256sum "$BIN" | cut -d' ' -f1)" = "$(cat "$here/capture/data/capture-binary.sha256")" ] || { echo "FAIL capture binary"; exit 2; }
t=$(mktemp)
python3 "$here/capture/gen_instance.py" "$here/capture/data/shen.invoke.dump" shen.invoke "$t" >/dev/null
cmp -s "$t" "$here/coq/CfCaptured.v" || { echo "FAIL instance differs from the dump"; rm -f "$t"; exit 3; }
rm -f "$t"
# The bytes in the dump are the bytes capture.c wrote out from the arena in the same run.
python3 - "$here" <<'P' || { echo "FAIL dump bytes differ from shen.invoke.bin"; exit 3; }
import sys
h=sys.argv[1]
b=[int(x) for x in [l for l in open(h+'/capture/data/shen.invoke.dump') if l.startswith('bytes')][0].split()[1:]]
raw=open(h+'/capture/data/shen.invoke.bin','rb').read()
sys.exit(0 if bytes(b)==raw[:len(b)] and not any(raw[len(b):]) else 1)
P
grep -nE '\bAdmitted\b|\badmit\b|^\s*Axiom|^\s*Parameter|^\s*Hypothesis [A-Za-z_]+ *: *False' "$here"/coq/*.v | grep -v '^.*(\*' && { echo "FAIL Admitted or axiom in sources"; exit 7; }
out=$(LIMIT=900 bash "$here/dbuild.sh" theories/Examples/emitter_risks_ns/CfAudit.vo 2>&1)
echo "$out" | grep -q '^rc=0' || { echo "FAIL build"; echo "$out" | head -5; exit 4; }
cd $W
# dune prints nothing when up to date, so compile the audit again for its output.
B=_build/default/theories
mkdir -p /tmp/s8a && rocq compile -Q $B LinuxProcessSemantics $B/Examples/emitter_risks_ns/CfAudit.v -o /tmp/s8a/CfAudit.vo > /tmp/s8audit.log 2>&1 || { echo "FAIL audit compile"; exit 4; }
s=$(date +%s)
ulimit -v 9000000
timeout 1200 rocqchk -silent -Q $B LinuxProcessSemantics ${VO:-$B/Examples/emitter_risks_ns/CfAudit.vo} > /tmp/s8chk.log 2>&1 || { echo "FAIL rocqchk"; tail -3 /tmp/s8chk.log; exit 5; }
echo "rocqchk rc=0 secs=$(( $(date +%s)-s ))"
bad=$(grep -E '^[A-Za-z_.]+ *:' /tmp/s8audit.log | sed -E 's/ *:.*//' | grep -vE '^(Axioms$|PrimInt63\.|PrimString\.|PrimArray\.)' | sort -u)
[ -z "$bad" ] || { echo "FAIL assumptions: $bad"; exit 6; }
n=$(grep -c 'Axioms:\|Closed under the global context' /tmp/s8audit.log)
echo "assumptions $(grep -E '^[A-Za-z_.]+ *:' /tmp/s8audit.log | sed -E 's/ *:.*//' | grep -v '^Axioms$' | sort -u | tr '\n' ' ')"
echo "audited blocks $n"
echo ALL_OK
