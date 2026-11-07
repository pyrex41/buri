#!/bin/bash
# In buri-lps. Gate for spike 9 item 1 (the C checker's binary): binds the proofs to the frozen runtime,
# builds the audit, requires the .vo files, replays with rocqchk (under flock), reads the assumptions.
# Exit codes: 2 runtime hash, 3 generated facts differ, 4 build or missing .vo, 5 rocqchk, 6 assumptions,
#             7 Admitted or an axiom in the sources, 0 ALL_OK.
here=$(cd "$(dirname "$0")" && pwd); W=${W:-/work-s9a}; export W; ex=$W/theories/Examples/s9bin_ns
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
R=${RUNTIME:-/tmp/s9/frozen/check-runtime}
[ "$(sha256sum "$R" | cut -d' ' -f1)" = 99300f3221ec53511d023f408e11ee6bd3b89f375ce36253d48a38a5a842955e ] || { echo "FAIL runtime hash"; exit 2; }
grep -nE '\bAdmitted\b|\badmit\b|^\s*Axiom|^\s*Parameter|^\s*Conjecture' "$here"/coq-bin/*.v && { echo "FAIL Admitted or axiom in sources"; exit 7; }
# regenerate the image and facts from the runtime; they must equal what the build uses
t=$(mktemp -d)
python3 "$here/bin-gen.py" "$R" "$t" >/dev/null || { echo "FAIL bin-gen"; exit 3; }
for f in s9bin_code.v SourceMemImage.v SourceMemImage_seg_000.hex; do
  [ -f "$ex/$f" ] && ! cmp -s "$t/$f" "$ex/$f" && { cp "$t/$f" "$ex/$f"; echo "regenerated $f"; }
  [ -f "$ex/$f" ] || cp "$t/$f" "$ex/$f"
done
rm -rf "$t"
out=$(LIMIT=${LIMIT:-3000} bash "$here/bin-dbuild.sh" theories/Examples/s9bin_ns/BinAudit.vo 2>&1)
echo "$out" | grep -q '^rc=0' || { echo "FAIL build"; echo "$out" | head -8; exit 4; }
cd $W; B=_build/default/theories
for f in DecContract DecModel RbContract BinAudit; do [ -f $B/Examples/s9bin_ns/$f.vo ] || { echo "MISSING $f"; exit 4; }; done
mkdir -p /tmp/s9bin_audit && rocq compile -Q $B LinuxProcessSemantics $B/Examples/s9bin_ns/BinAudit.v -o /tmp/s9bin_audit/BinAudit.vo > /tmp/s9bin_audit.log 2>&1 || { echo "FAIL audit compile"; exit 4; }
s=$(date +%s); ulimit -v 9000000
flock /tmp/s9/rocqchk.lock timeout 2400 rocqchk -silent -Q $B LinuxProcessSemantics $B/Examples/s9bin_ns/BinAudit.vo > /tmp/s9bin_chk.log 2>&1 || { echo "FAIL rocqchk"; tail -3 /tmp/s9bin_chk.log; exit 5; }
echo "rocqchk rc=0 secs=$(( $(date +%s)-s ))"
bad=$(grep -E '^[A-Za-z_.]+ *:' /tmp/s9bin_audit.log | sed -E 's/ *:.*//' | grep -vE '^(Axioms$|PrimInt63\.|PrimString\.|PrimArray\.)' | sort -u)
[ -z "$bad" ] || { echo "FAIL assumptions: $bad"; exit 6; }
echo "assumptions $(grep -E '^[A-Za-z_.]+ *:' /tmp/s9bin_audit.log | sed -E 's/ *:.*//' | grep -v '^Axioms$' | sort -u | tr '\n' ' ')"
echo "audited blocks $(grep -c 'Axioms:\|Closed under the global context' /tmp/s9bin_audit.log)"
echo ALL_OK
