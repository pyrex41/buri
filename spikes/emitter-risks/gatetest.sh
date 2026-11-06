#!/bin/bash
# In buri-lps. Shows each failure case of check.sh fires, from a modified copy, and that the clean case passes.
here=$(cd "$(dirname "$0")" && pwd)
case_() { # name, expected exit, setup in the copy, env
  m=$(mktemp -d); cp -a "$here"/. "$m"/
  ( cd "$m" && eval "$3" )
  env $4 W=/work-s8m bash "$m/check.sh" > /tmp/gt.log 2>&1; rc=$?
  [ "$rc" = "$2" ] && echo "fired $1: exit $rc ($(grep -m1 -E 'FAIL|ALL_OK' /tmp/gt.log))" || { echo "WRONG $1: exit $rc, expected $2"; tail -3 /tmp/gt.log; }
  rm -rf "$m"
}
case_ clean-before 0 "true"
cp /lps/s8/cap/capture /tmp/s8-capture-bad; printf x >> /tmp/s8-capture-bad
case_ wrong-capture-binary 2 "true" "CAPTURE_BIN=/tmp/s8-capture-bad"
case_ dump-and-bin-disagree 3 "python3 patch_dump.py capture/data/shen.invoke.dump capture/data/shen.invoke.dump bytes 2a 00498513 && python3 capture/gen_instance.py capture/data/shen.invoke.dump shen.invoke coq/CfCaptured.v"
case_ instance-not-regenerated 3 "sed -i 's/c_arity := 2/c_arity := 3/' coq/CfCaptured.v"
case_ broken-proof 4 "sed -i '0,/exact cap_wfk\\./s//exact tag_true./' coq/CfInstance.v"
case_ rocqchk-fails 5 "true" "VO=/nonexistent.vo"
case_ smuggled-assumption 6 "printf 'From Stdlib Require Import Classical.\\nPrint Assumptions classic.\\n' >> coq/CfAudit.v"
case_ admitted 7 "sed -i 's/^Lemma cap_wfk/Lemma extra : False. Admitted.\nLemma cap_wfk/' coq/CfInstance.v"
case_ clean-after 0 "true"
