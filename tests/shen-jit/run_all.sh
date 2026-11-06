#!/bin/bash
# In the buri-lps container: compile the model and run all three differential sets.
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
TAILN=8 bash /tmp/p1/c.sh JitFloat JitBytecode JitMeta 2>&1 | grep -vE "register-all|nested using|Scheme All|^File.*line 1[0-9][0-9]," | cut -c1-260
ls -la --time-style=+%T /tmp/p1/*.vo | cut -c24-
d=/tmp/p1/d; mkdir -p $d; cd $d
cat /lps/s4/sj/tests/kl/ops.kl /buri/tests/shen-jit/ops-calls.kl > ops-all.kl
sed "s/^From Coq Require/From Stdlib Require/" /buri/tests/shen-jit/JitDiffLib.v > JitDiffLib.v
rocq compile -Q /tmp/p1 Buri -Q . JitDiff JitDiffLib.v 2>&1 | grep -A8 "Error" | cut -c1-200
for s in "ev /lps/s4/sj/tests/kl/eval-cases.kl kl" "ops $d/ops-all.kl kl" "ct /lps/s4/sj/contract/examples.shen contract"; do
  set -- $s
  nohup bash /buri/tests/shen-jit/run_case.sh $1 $2 $3 > $d/log_$1.txt 2>&1 &
done
wait
echo ALL_SETS_DONE
