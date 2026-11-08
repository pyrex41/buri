#!/bin/bash
# Split census, step 2 (spikes/pass-split/CENSUS.md): run the existing stage 0 judge
# (rocq/JitLowerStage0.v, as scripts/check-shen-jit.sh runs it) on each file's definitions three
# times, against the stored code objects (<f>.sbc): as read (<f>.forms, variant src), as the
# erased normal form (<f>.nforms, variant nf) and as the erased normal form with the inlining
# marker dropped (<f>.tforms, variant tf), both from capture_passes.sh. Runs in the buri-lps
# container.
#
#   judge_split.sh ROCQ_DIR STAGE0_DIR WITNESS_DIR OUT_DIR
#
# ROCQ_DIR holds Buri's compiled JitLower*.vo (as check-shen-jit.sh's $out). For each file and
# variant (src, nf, tf) OUT_DIR/<variant>/<f>.codes gets the tally line and one verdict per definition,
# in file order: 1 accepted, 2 rejected, 0 unreadable. The verdicts come from the same `judge`;
# the only addition to the generated file is printing judge_all's verdicts as numbers.
# Acceptance on the erased form is evidence about the emit side only: the erasure is untrusted
# and no front end proof is involved.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
rocq_dir=$1; s0=$2; wit=$3; out=$4
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
mkdir -p "$out"
for variant in src nf tf; do
  d="$out/$variant"; mkdir -p "$d/in"
  for f in $(cd "$s0" && ls *.forms | sed 's/\.forms$//'); do
    case $variant in
      src) cp "$s0/$f.forms" "$d/in/$f.forms" ;;
      nf) cp "$wit/$f.nforms" "$d/in/$f.forms" ;;
      tf) cp "$wit/$f.tforms" "$d/in/$f.forms" ;;
    esac
    cp "$s0/$f.sbc" "$d/in/$f.sbc"
  done
done
run_one() { # variant file
  local variant=$1 f=$2 d="$out/$1" id
  id=$(echo "$f" | tr - _)
  python3 "$here/stage0_to_rocq.py" "$d/in" "$f" "$d/S0_$id.v" || { echo "READ_FAILED $variant $f"; return 1; }
  sed -i 's/^From Coq Require/From Stdlib Require/' "$d/S0_$id.v"
  cat >> "$d/S0_$id.v" <<EOF
Definition codes_$id := Eval vm_compute in
  map (fun v => match v with Accepted _ => 1%nat | Rejected _ => 2%nat | Unparsed => 0%nat end)
      (judge_all forms_$id sbc_$id).
Print codes_$id.
EOF
  (cd "$d" && timeout 1800 rocq compile -Q "$rocq_dir" Buri "S0_$id.v" > "S0_$id.log" 2>&1) || { tail -5 "$d/S0_$id.log"; echo "ROCQ_FAILED $variant $f"; return 1; }
  local log; log=$(tr '\n' ' ' < "$d/S0_$id.log")
  local c v
  c=$(echo "$log" | grep -oE "result_$id = *\([0-9]+, [0-9]+, [0-9]+" | sed 's/.*(//; s/,//g')
  v=$(echo "$log" | grep -oE "codes_$id = *\[[0-9; ]*\]" | sed 's/.*\[//; s/\]//; s/;/ /g' | tr -s ' ')
  [ -n "$c" ] && [ -n "$v" ] || { echo "NO_RESULT $variant $f"; return 1; }
  echo "$f $c" > "$d/$f.codes"; echo "$v" >> "$d/$f.codes"
}
export -f run_one; export here out rocq_dir
fail=0
for variant in src nf tf; do
  for f in $(cd "$s0" && ls *.forms | sed 's/\.forms$//'); do echo "$variant $f"; done
done | xargs -P "${JOBS:-6}" -n 2 bash -c 'run_one "$0" "$1"' || fail=1
for variant in src nf tf; do
  cat "$out/$variant"/*.codes 2>/dev/null | awk 'NR%2==1' | sort > "$out/$variant.counts"
done
[ $fail = 0 ] && echo "JUDGE_SPLIT_DONE" || { echo "JUDGE_SPLIT_FAILED"; exit 1; }
