#!/bin/bash
# Second step of the sail-arm Coq probe: compile armv9.v (42 MB) once
# armv9_types.vo and arm_extras.vo exist.  -R (not -Q) because the snapshot
# uses unqualified `Require Import armv9_types`.
set -uo pipefail
A=/tmp/claude-0/-home-user-buri/2c5c340f-028f-583d-92bc-9357951dc84f/scratchpad/arm
COQ=/nix/store/z93aiwvyich2swj7qx9ahccwj15hzx8y-coq-8.18.0
STDPP=/nix/store/xz8bq0nyg9j6b37pja9qxvbj4w15wmqf-coq8.18-stdpp-1.10.0
TIME=/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time
export PATH="$COQ/bin:$PATH"
export COQPATH="$STDPP/lib/coq/8.18/user-contrib"
ulimit -s unlimited
ulimit -v 12582912
cd "$A/sail-arm-coq"
Q=(-Q "$A/src/coq-sail-0.19/src-stdpp" SailStdpp -R . SailArm)
for f in armv9_types arm_extras; do
  [ -f "$f.vo" ] || { "$TIME" -v coqc "${Q[@]}" "$f.v" > "$f.log" 2>&1; echo "$f rc=$?"; }
done
"$TIME" -v timeout "${ARMV9_TIMEOUT:-3600}" coqc "${Q[@]}" armv9.v > armv9.log 2>&1
echo "armv9 rc=$?"; grep -E 'Elapsed|Maximum resident|Exit status' armv9.log; grep -m5 -i -B2 -A8 'error' armv9.log
