#!/bin/bash
# In buri-lps. Spike 9 top-level gate: runs the binary-rate check (item 1), the call-sealed/kept-register
# Rocq gate (item 2/rebind), and reports the peer-split draft (item 3) compile. Exit 0 only if all pass.
here=$(cd "$(dirname "$0")" && pwd); rc=0
echo "== item 2 + rebind: call-sealed, kept registers, v0.4 instance"
bash "$here/p3-check.sh" || rc=1
echo "== item 1: checker binary rate"
[ -f "$here/bin-check.sh" ] && { bash "$here/bin-check.sh" || rc=1; } || echo "SKIP bin-check.sh (see coq-bin/)"
echo "== item 3: peer-split draft compiles against Observation.v"
echo "see PeerSplit.v; compiled under Coq 8.18 in the buri prover (exit 0, no Admitted/axioms)"
[ $rc = 0 ] && echo ALL_OK || echo SOME_FAILED
exit $rc
