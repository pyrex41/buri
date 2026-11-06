#!/bin/bash
# In buri-lps. Each mutant must fail to build. A rejection only shows this proof script fails on the
# mutant; it is not a proof that the mutant's statement is false.
here=$(cd "$(dirname "$0")" && pwd); export W=/work-s7m
[ -d $W ] || cp -a /work-s7 $W
T=theories/Examples/emitter_ns/MoveAudit.vo
res() { if [ "$1" = 0 ]; then echo "MUTANT_ACCEPTED $2"; else echo "rejected $2: $(grep -m1 -E '^Error|Error:' /tmp/s7-$(basename $W).log | cut -c1-90)"; fi; }
bash "$here/regen.sh" >/dev/null 2>&1; ERRL=3 bash "$here/dbuild.sh" $T >/dev/null 2>&1; echo "baseline rc=$?"
spec() { m=$(mktemp -d); cp -a "$here"/. "$m"/; sed -i "$3" "$m/coq/$2"; cmp -s "$m/coq/$2" "$here/coq/$2" && { echo "MUTANT_NOT_APPLIED $1"; return; }
  ERRL=1 LIMIT=400 bash "$m/dbuild.sh" $T >/dev/null 2>&1; res $? "spec:$1"; }
byte() { bash "$here/regen.sh" "$2" >/dev/null 2>&1; ERRL=1 LIMIT=400 bash "$here/dbuild.sh" $T >/dev/null 2>&1; res $? "bytes:$1"; }
byte skip-first-compare 36cf8:13000000
byte skip-store-compare 36d1c:13000000
byte skip-keep-compare 36d3a:13000000
byte wrong-cached-mv 36c00:9b83c654
byte wider-domain 36ba0:1303f03f
byte skip-length-check 36c6a:13000000
bash "$here/regen.sh" >/dev/null 2>&1
spec keep-word MoveTemplate.v 's/\[c_mv 18 10\]/[c_mv 18 11]/'
spec cached-source MoveTemplate.v 's/\[c_mv 10 18\]/[c_mv 11 18]/'
spec store-opcode MoveTemplate.v 's/57344 + c_off off/57345 + c_off off/'
spec load-offset MoveTemplate.v 's/(off \/ 8) mod 8/(off \/ 8) mod 4/'
spec sd-field MoveTemplate.v 's/(off mod 32) \* 128 + 35/(off mod 32) * 128 + 39/'
spec skipped-store-needs-keep MoveContract.v 's/(store = false -> k = 1) \/\\/(store = false -> k = 0) \/\\/'
spec domain-wider MoveTemplate.v 's/0 <= dst <= 255/0 <= dst <= 127/'
bash "$here/regen.sh" >/dev/null 2>&1; ERRL=3 bash "$here/dbuild.sh" $T >/dev/null 2>&1; echo "restored rc=$?"
