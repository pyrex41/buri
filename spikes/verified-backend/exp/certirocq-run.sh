#!/bin/bash
# Spike 10, in buri-vb-certirocq after setup-certirocq.sh: compile vb.bench (Búri's KLSemantics.next
# driving the test definitions) with CertiRocq to C, then gcc -O2, and time it.
#   certirocq-run.sh N [EXTRA.kl]
set -eu
export OPAMROOTISOK=1; eval $(opam env --switch=certirocq --set-switch) 2>/dev/null
N=$1; EXTRA=${2:-}
C=/opt/certirocq; W=/root/vbc; B=/root/buri91
if [ ! -f $B/KLSemantics.vo ]; then   # Búri's semantics under Rocq 9.1 (/buri is the repo, read-only)
  mkdir -p $B && cp /buri/rocq/{Observation,KLSyntax,KLValue,KLSemantics}.v $B/
  (cd $B && sed -i 's/^From Coq Require/From Stdlib Require/' *.v &&
   for f in Observation KLSyntax KLValue KLSemantics; do rocq compile -Q . Buri $f.v; done)
fi
mkdir -p $W && cd $W
python3 -I /spike/exp/kl2rocq.py $N VbC.v /spike/exp/defs.kl /spike/exp/driver.kl $EXTRA
sed -i 's/^From Coq Require/From Stdlib Require/' VbC.v
cat >> VbC.v <<'R'
From CertiRocq.Plugin Require Import CertiRocq.
CertiRocq Compile result.
CertiRocq Generate Glue --output "glue_vb" [ Z, positive ].
R
s=$(date +%s%N); rocq compile -Q $B Buri -R $C/plugins/plugin CertiRocq.Plugin -I $C/plugins/plugin VbC.v > compile.log 2>&1 || { tail -20 compile.log; exit 3; }
echo "rocq+certirocq: $(( ($(date +%s%N)-s)/1000000 )) ms"
ls *.c *.h
cat > main.c <<'M'
#include <stdio.h>
#include "gc_stack.h"
#include "glue_vb.h"
extern value body(struct thread_info *);
int main(void) { struct thread_info *t = make_tinfo(); value v = body(t);
  print_Corelib_Numbers_BinNums_Z(v); printf("\n"); return 0; }
M
CF=$(ls *VbC*result*.c 2>/dev/null || ls VbC.result.c)
s=$(date +%s%N); gcc -O2 -fomit-frame-pointer -w -I$C/runtime -o vb main.c glue_vb.c $CF $C/runtime/gc_stack.c $C/runtime/prim_int63.c $C/runtime/prim_floats.c $C/runtime/prim_string.c -lm 2>&1 | tail -5
echo "gcc: $(( ($(date +%s%N)-s)/1000000 )) ms"
for i in 1 2 3; do s=$(date +%s%N); ./vb; echo "run: $(( ($(date +%s%N)-s)/1000000 )) ms"; done
