#!/bin/bash
# Stage 0 source judge over emit hooks (task r22-emit-check). Runs, per stage 0 file, Rocq's
# JitEmitCheck.judge_emit_all with the hooks of a HOOK MODULE (rocq/<HOOKMOD>.v, whose Module
# HOOKMOD defines `hooks : JitEmitCheck.Hooks`), beside the existing judge
# (JitLowerStage0.judge_all), against the stored code objects (<f>.sbc) and forms as read
# (<f>.forms). Each emit family runs its stage 0 counts with its own hook module; the base hooks
# are JitEmitCheck's own (HOOKMOD=JitEmitCheck).
#
#   judge_hooks.sh HOOKMOD ROCQ_DIR STAGE0_DIR OUT_DIR [EXPECTED_COUNTS]
#
# ROCQ_DIR holds Buri's compiled modules up to JitEmitCheck (scripts/check-shen-jit.sh's $out, or a
# dev build). If ROCQ_DIR has no HOOKMOD.vo, rocq/HOOKMOD.v is compiled into it first.
# OUT_DIR/<f>.codes gets "<f> accepted rejected unreadable" (hook judge), then the existing judge's
# verdict codes and the hook judge's, one per definition in file order (1 accepted, 2 rejected,
# 0 unreadable). OUT_DIR/counts.txt is sorted like tests/shen-jit/stage0-accepted.txt and is
# compared with EXPECTED_COUNTS (default: that file, for HOOKMOD=JitEmitCheck; none otherwise).
# Fails if any definition the existing judge accepts is not accepted by the hook judge (LOST), if
# the base hooks gain any definition, or if the counts differ from EXPECTED_COUNTS.
# Verdicts are Rocq's (vm_compute); this script only compares printed numbers. The counts are
# source-judge counts: they are not "validated" (full-pipeline) counts. Runs in buri-lps; every
# Rocq compile goes through /lps/bin/rocq-slot when it exists; JOBS (default 2) files at a time.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
[ $# -ge 4 ] || { sed -n '2,21p' "$0"; exit 2; }
hook=$1; rocq_dir=$(cd "$2" && pwd); s0=$3; out=$4
expected=${5:-}
[ -z "$expected" ] && [ "$hook" = JitEmitCheck ] && expected="$here/stage0-accepted.txt"
eval "$(opam env --switch=lps --set-switch)" 2>/dev/null
slot=; [ -x /lps/bin/rocq-slot ] && slot=/lps/bin/rocq-slot
mkdir -p "$out"; out=$(cd "$out" && pwd)
[ -f "$rocq_dir/JitEmitCheck.vo" ] || { echo "NO_JITEMITCHECK in $rocq_dir"; exit 3; }
if [ ! -f "$rocq_dir/$hook.vo" ]; then
  [ -f "$root/rocq/$hook.v" ] || { echo "NO_HOOK_MODULE $hook"; exit 3; }
  sed 's/^From Coq Require/From Stdlib Require/' "$root/rocq/$hook.v" > "$rocq_dir/$hook.v"
  (cd "$rocq_dir" && $slot timeout 1800 rocq compile -Q . Buri "$hook.v" > "$hook.log" 2>&1) || { tail -20 "$rocq_dir/$hook.log"; echo "HOOK_ROCQ_FAILED $hook"; exit 4; }
fi
run_one() { # file
  local f=$1 id log c o h
  id=$(echo "$f" | tr - _)
  python3 "$here/stage0_to_rocq.py" --hooks "$s0" "$f" "$out/H_$id.v" "$hook" || { echo "READ_FAILED $f"; return 1; }
  sed -i 's/^From Coq Require/From Stdlib Require/' "$out/H_$id.v"
  (cd "$out" && $slot timeout 1800 rocq compile -Q "$rocq_dir" Buri "H_$id.v" > "H_$id.log" 2>&1) || { tail -5 "$out/H_$id.log"; echo "ROCQ_FAILED $f"; return 1; }
  log=$(tr '\n' ' ' < "$out/H_$id.log")
  c=$(echo "$log" | grep -oE "hcount_$id = *\(*[0-9]+%?n?a?t?, [0-9]+%?n?a?t?, [0-9]+" | sed 's/.*= *(*//; s/%nat//g; s/,//g')
  o=$(echo "$log" | grep -oE "ocodes_$id = *\[[0-9%nat; ]*\]" | sed 's/.*\[//; s/\]//; s/%nat//g; s/;/ /g' | tr -s ' ')
  h=$(echo "$log" | grep -oE "hcodes_$id = *\[[0-9%nat; ]*\]" | sed 's/.*\[//; s/\]//; s/%nat//g; s/;/ /g' | tr -s ' ')
  [ -n "$c" ] && [ -n "$o" ] && [ -n "$h" ] || { echo "NO_RESULT $f"; return 1; }
  printf '%s %s\n%s\n%s\n' "$f" "$c" "$o" "$h" > "$out/$f.codes"
}
export -f run_one; export here out rocq_dir s0 hook slot
rm -f "$out"/*.codes
fail=0
(cd "$s0" && ls *.forms | sed 's/\.forms$//') | xargs -P "${JOBS:-2}" -n 1 bash -c 'run_one "$0"' || fail=1
[ $fail = 0 ] || { echo "JUDGE_HOOKS_FAILED"; exit 1; }
cat "$out"/*.codes | awk 'NR%3==1' | sort > "$out/counts.txt"
python3 -I - "$out" "$hook" <<'CMP' || fail=1
import sys, pathlib
out = pathlib.Path(sys.argv[1]); hook = sys.argv[2]
tot = dict(old=0, new=0, gained=0, lost=0, defs=0)
lines = []
for p in sorted(out.glob('*.codes')):
    head, o, h = p.read_text().splitlines()[:3]
    o, h = o.split(), h.split()
    if len(o) != len(h):
        print('LENGTH_MISMATCH', p.name); sys.exit(1)
    f = head.split()[0]
    for i, (a, b) in enumerate(zip(o, h)):
        tot['defs'] += 1; tot['old'] += a == '1'; tot['new'] += b == '1'
        if a == '1' and b != '1': tot['lost'] += 1; lines.append('LOST %s #%d' % (f, i))
        if a != '1' and b == '1': tot['gained'] += 1; lines.append('GAINED %s #%d' % (f, i))
(out / 'diff.txt').write_text('\n'.join(lines) + ('\n' if lines else ''))
print('hook judge (%s): %d of %d stage 0 definitions accepted by the source judge with hooks; existing judge %d; gained %d, lost %d'
      % (hook, tot['new'], tot['defs'], tot['old'], tot['gained'], tot['lost']))
bad = tot['lost'] > 0 or (hook == 'JitEmitCheck' and tot['gained'] > 0)
sys.exit(1 if bad else 0)
CMP
if [ -n "$expected" ]; then
  diff "$expected" "$out/counts.txt" > "$out/counts-diff.txt" || { cat "$out/counts-diff.txt"; echo "COUNTS_CHANGED"; fail=1; }
fi
[ $fail = 0 ] && echo "JUDGE_HOOKS_OK" || { echo "JUDGE_HOOKS_FAILED"; exit 1; }
