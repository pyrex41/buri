#!/bin/bash
# Try to check the sail-arm arm-v9.4-a Coq snapshot (sail-arm 7d058164) with
# nixpkgs Coq 8.18.0 + stdpp 1.10.0 + coq-sail-stdpp 0.19.  Separate from the
# repository's pinned Coq toolchain; nothing here is a Buri proof.
set -uo pipefail
A=/tmp/claude-0/-home-user-buri/2c5c340f-028f-583d-92bc-9357951dc84f/scratchpad/arm
COQ=/nix/store/z93aiwvyich2swj7qx9ahccwj15hzx8y-coq-8.18.0
STDPP=/nix/store/xz8bq0nyg9j6b37pja9qxvbj4w15wmqf-coq8.18-stdpp-1.10.0
MAKE=/nix/store/vs2sa1msvkjxbb70h47819zq8a9srj21-gnumake-4.4.1/bin/make
export PATH="$COQ/bin:$PATH"
export COQPATH="$STDPP/lib/coq/8.18/user-contrib"
coqc --version
ulimit -s unlimited
# 12 GiB address-space cap per coqc so a runaway compile cannot take the host.
ulimit -v 12582912
cd "$A/src/coq-sail-0.19/src-stdpp"
/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time -v "$MAKE" -j2 HAVE_OPAM_BBV=no BBV_DIR= all > "$A/coq-sail-build.log" 2>&1
echo "coq-sail-stdpp rc=$?"
tail -3 "$A/coq-sail-build.log"
W="$A/sail-arm-coq"
mkdir -p "$W"
cp "$A/src/sail-arm/arm-v9.4-a/snapshots/coq/"*.v "$W/"
cd "$W"
SAILQ=(-Q "$A/src/coq-sail-0.19/src-stdpp" SailStdpp -Q . SailArm)
for f in armv9_types arm_extras; do
  /nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time -v timeout 3600 coqc "${SAILQ[@]}" "$f.v" > "$f.log" 2>&1
  echo "$f rc=$?"; grep -E 'Elapsed|Maximum resident' "$f.log"; grep -m3 -i error "$f.log"
done
/nix/store/b140qkky12n2fskhviv352sh9hphx0m9-time-1.10/bin/time -v timeout "${ARMV9_TIMEOUT:-2700}" coqc "${SAILQ[@]}" armv9.v > armv9.log 2>&1
echo "armv9 rc=$?"; grep -E 'Elapsed|Maximum resident' armv9.log; grep -m5 -i -B2 -A5 error armv9.log
