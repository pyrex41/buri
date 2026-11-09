#!/bin/sh
# Write gen/Stage0Gen/S0_<file>.lean for every row of tests/shen-jit/stage0-accepted.txt.
#   tools/gen_stage0.sh [STAGE0_DIR]     (default /lps/p4/sj/build/stage0, as check-shen-jit.sh)
set -e
cd "$(dirname "$0")/.."
d=${1:-/lps/p4/sj/build/stage0}
mkdir -p gen/Stage0Gen
while read name a r u; do
  python3 tools/stage0_to_lean.py "$d" "$name" "gen/Stage0Gen/S0_$(echo "$name" | tr '-' '_').lean" "$a" "$r" "$u"
done < ../tests/shen-jit/stage0-accepted.txt
ls gen/Stage0Gen | wc -l
