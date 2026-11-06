#!/bin/bash
# In buri-lps. Shows check.sh fires. Each case runs on a temporary copy of this directory, in /work-s7m.
here=$(cd "$(dirname "$0")" && pwd); export W=/work-s7m
[ -d $W ] || cp -a /work-s7 $W
run() { # name expected-exit [env ...]; the copy is in $m
  name=$1; want=$2; shift 2
  env "$@" bash "$m/check.sh" >/tmp/gt.log 2>&1; rc=$?
  [ "$rc" = "$want" ] && echo "fired $name rc=$rc" || { echo "WRONG $name rc=$rc want $want"; tail -3 /tmp/gt.log; }
}
fresh() { m=$(mktemp -d); cp -a "$here"/. "$m"/; }
fresh; run clean 0 X=1
fresh; run wrong-binary 2 RUNTIME=/lps/s7/out/base/runtime
fresh; echo 0000 > "$m/checker-bytes.sha256"; run wrong-checker-bytes 3 X=1
fresh; printf 'Theorem bad : False.\nProof. Admitted.\n' >> "$m/coq/MoveAudit.v"; run admitted 7 X=1
fresh; printf 'Garbage here.\n' >> "$m/coq/MoveAudit.v"; run broken-proof 4 X=1
fresh; printf 'Local Axiom bad : False.\nTheorem t : False.\nProof. exact bad. Qed.\nPrint Assumptions t.\n' >> "$m/coq/MoveAudit.v"; run smuggled-axiom 6 X=1
fresh; run clean-again 0 X=1
