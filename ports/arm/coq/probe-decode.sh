#!/bin/bash
A=/tmp/claude-0/-home-user-buri/2c5c340f-028f-583d-92bc-9357951dc84f/scratchpad/arm
export PATH="/nix/store/z93aiwvyich2swj7qx9ahccwj15hzx8y-coq-8.18.0/bin:$PATH"
export COQPATH="/nix/store/xz8bq0nyg9j6b37pja9qxvbj4w15wmqf-coq8.18-stdpp-1.10.0/lib/coq/8.18/user-contrib"
ulimit -s unlimited
ulimit -v 12582912
cd "$A/sail-arm-coq"
/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time -v timeout "${T:-1800}" coqc -Q "$A/src/coq-sail-0.19/src-stdpp" SailStdpp -R . SailArm "${1:-BuriDecodeProbe.v}" 2>&1 | grep -v -E '^\s+(Average|Socket|Signals|Swaps|File system|Page size|Voluntary|Involuntary|Major|Minor|Percent|Exit|Command|User|System)'
