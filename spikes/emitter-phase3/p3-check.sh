#!/bin/bash
# In buri-lps. The gate for spike 9's Rocq part (coq-p3/): binds the instance to the captured bytes and the
# binary that made them, builds every statement, requires the .vo files, replays with rocqchk, and reads the
# assumptions.  Exit codes: 2 capture binary hash, 3 instance differs from the dump, 4 build or missing .vo,
# 5 rocqchk, 6 assumptions, 7 Admitted or an axiom in the sources, 0 ALL_OK.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s9b}; export W
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
D=$here/capture/data9
BIN=${CAPTURE_BIN:-/tmp/s9/cap/capture}
[ "$(sha256sum "$BIN" | cut -d' ' -f1)" = "$(cat "$D/capture-binary.sha256")" ] || { echo "FAIL capture binary"; exit 2; }
t=$(mktemp)
python3 "$here/capture/gen_instance9.py" "$D/shortnatters.raw" "$D/shortnatters.bin" "$D/shortnatters.cert" "$t" >/dev/null
cmp -s "$t" "$here/coq-p3/CfCaptured9.v" || { echo "FAIL instance differs from the dump"; rm -f "$t"; exit 3; }
rm -f "$t"
# The dump's bytes are the arena block capture.c wrote in the same run (/tmp/s9/cap), when that run is present.
if [ -f "/tmp/s9/cap/shen.<shortnatters>.bin" ]; then
  cmp -s "/tmp/s9/cap/shen.<shortnatters>.bin" "$D/shortnatters.bin" || { echo "FAIL dump bytes differ from the capture run"; exit 3; }
fi
grep -nE '\bAdmitted\b|\badmit\b|^\s*Axiom|^\s*Parameter|^\s*Hypothesis [A-Za-z_]+ *: *False' "$here"/coq-p3/*.v | grep -v '^.*(\*' && { echo "FAIL Admitted or axiom in sources"; exit 7; }
out=$(LIMIT=1800 bash "$here/p3-dbuild.sh" theories/Examples/emitter_p3_ns/CfAudit.vo 2>&1)
echo "$out" | grep -q '^rc=0' || { echo "FAIL build"; echo "$out" | head -5; exit 4; }
cd $W
B=_build/default/theories
mkdir -p /tmp/s9p3a && rocq compile -Q $B LinuxProcessSemantics $B/Examples/emitter_p3_ns/CfAudit.v -o /tmp/s9p3a/CfAudit.vo > /tmp/s9p3audit.log 2>&1 || { echo "FAIL audit compile"; exit 4; }
s=$(date +%s)
ulimit -v 9000000
( flock 9; timeout 1800 rocqchk -silent -Q $B LinuxProcessSemantics ${VO:-$B/Examples/emitter_p3_ns/CfAudit.vo} > /tmp/s9p3chk.log 2>&1 ) 9>/tmp/s9/rocqchk.lock || { echo "FAIL rocqchk"; tail -3 /tmp/s9p3chk.log; exit 5; }
echo "rocqchk rc=0 secs=$(( $(date +%s)-s ))"
bad=$(grep -E '^[A-Za-z_.]+ *:' /tmp/s9p3audit.log | sed -E 's/ *:.*//' | grep -vE '^(Axioms$|PrimInt63\.|PrimString\.|PrimArray\.)' | sort -u)
[ -z "$bad" ] || { echo "FAIL assumptions: $bad"; exit 6; }
n=$(grep -c 'Axioms:\|Closed under the global context' /tmp/s9p3audit.log)
echo "assumptions $(grep -E '^[A-Za-z_.]+ *:' /tmp/s9p3audit.log | sed -E 's/ *:.*//' | grep -v '^Axioms$' | sort -u | tr '\n' ' ')"
echo "audited blocks $n"
echo ALL_OK
