#!/bin/bash
# Pass capture driver (spikes/pass-split/CENSUS.md). Runs in the buri-lps container:
#
#   capture_passes.sh OUT_DIR [SJ_DIR [BIN]]
#
# SJ_DIR defaults to /lps/p4/sj (the pinned Shen/JIT d3348ce with build/stage0), BIN to its
# build/shen-jit, which must be the named binary of toolchain.lock.json. Nothing is written
# outside OUT_DIR; the guest runs with OUT_DIR/run as its working directory.
#
# Three runs of tests/shen-jit/capture_passes.shen under BIN, each lowering all 950 stage 0
# definitions and printing [defun F Code] for comparison with the stored stage 0 line:
#   witness  the build's own lowerer, build/tools/lower.shen, loaded into the guest exactly as
#            src/lowerer/stage0.shen loads it. Writes the witnesses (below). Every .sbc and .forms
#            line must equal the stored one byte for byte, or the run fails.
#   count    a counting copy of the same lowerer (instrument_lower.py); must also reproduce every
#            stored line byte for byte before its counts (<f>.ticks) are used.
#   image    the lowerer sealed in BIN itself (capture_image_shim.shen); a measurement only.
#
# Witness formats, one line per definition, in the order of <f>.forms, in stage 0's output
# syntax (src/lowerer/stage0.shen; read by tests/shen-jit/stage0_to_rocq.py's tokenizer):
#   <f>.share   (defun F (P1 ... Pn) S)     S = (share Body), KLambda
#   <f>.norm    (F (P1 ... Pn) N)           N = (norm (P1 ... Pn) S), nodes as lists:
#       (const V)  V is a datum: a symbol, number, string, true/false, () or a list
#                  (a folded constant list, printed as a list); never a node
#       (var X)  (if C X Y)  (and X Y)  (or X Y)  (let X V Body)  (do X Y)
#       (lambda X Body)  (freeze Body)  (prim Op (A1 ... An))  (call F (A1 ... An))
#       (apply F)  (apply F X)  (trap X E Handler)
#     Args of prim and call are one list, () when empty. Variables the lowerer made are named
#     stage0.lower.argN / stage0.lower.elseN / stage0.lower.exceptionN (the build's renamed
#     lowerer; N restarts at 1 per definition and counts on from share into norm). The binder
#     stage0.lower.inlining in (let stage0.lower.inlining (const F) Body) marks an inlined body
#     of F: emission gives it no slot and lowers Body in place (lower.shen, expr and test).
#   <f>.nforms  (defun F (P1 ... Pn) K)     K = erase(N), census only, untrusted (see
#     capture_passes.shen, pc.erase)
#   <f>.ncensus (F (Flags...))              folded shadow applyhead callshadow inlined?
#                                           inlining-marker fresh
#   <f>.ticks   (F ((Key Count) ...))       rewrite counts from the count run
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1; sj=${2:-/lps/p4/sj}; bin=${3:-$sj/build/shen-jit}
root=$(cd "$here/../.." && pwd)
want=$(python3 -c "import json;print(json.load(open('$root/toolchain.lock.json'))['shen_jit']['binary_sha256'])")
got=$(sha256sum "$bin" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "NOT_THE_NAMED_BINARY $got"; exit 3; }
s0=$sj/build/stage0
rm -rf "$out"; mkdir -p "$out/run" "$out/witness" "$out/count" "$out/image"
python3 "$here/instrument_lower.py" "$sj/src/lowerer/lower.shen" "$out/lower-count.shen" || exit 4
# The build's lowerer is lower.shen renamed (Makefile, build/tools/%.shen); check that it still is.
python3 -c "
import sys; sys.path.insert(0, '$here'); import instrument_lower as m
sys.exit(0 if m.rename(open('$sj/src/lowerer/lower.shen').read()) == open('$sj/build/tools/lower.shen').read() else 1)" \
  || { echo "BUILD_LOWERER_NOT_RENAMED_SOURCE"; exit 4; }
run() { # mode lowerer dir
  (cd "$out/run" && timeout 1800 qemu-riscv64 "$bin" script "$here/capture_passes.shen" "$sj" "$2" "$out/$3/" "$1" \
     > "$out/$3.log" 2>&1)
  local rc=$?; tail -1 "$out/$3.log" | grep -q '^capture done' && [ $rc = 0 ] || { tail "$out/$3.log"; echo "CAPTURE_FAILED $3 rc=$rc"; exit 5; }
}
compare() { # dir -> differing .sbc lines, total
  local n=0 f
  for f in $(cd "$s0" && ls *.forms | sed 's/\.forms$//'); do
    n=$((n + $(paste -d '\t' "$s0/$f.sbc" "$out/$1/$f.sbc" | awk -F '\t' '$1 != $2' | wc -l)))
    cmp -s "$s0/$f.forms" "$out/$1/$f.forms" || { echo "FORMS_DIFFER $1 $f"; exit 6; }
    [ "$(wc -l < "$s0/$f.sbc")" = "$(wc -l < "$out/$1/$f.sbc")" ] || { echo "COUNT_DIFFERS $1 $f"; exit 6; }
  done
  echo $n
}
run witness "$sj/build/tools/lower.shen" witness
run count "$out/lower-count.shen" count
run witness "$here/capture_image_shim.shen" image
total=$(cat "$s0"/*.sbc | wc -l)
w=$(compare witness); c=$(compare count); i=$(compare image)
echo "definitions: $total"
echo "witness run: $((total - w)) of $total code objects byte-identical to stage 0"
echo "count run:   $((total - c)) of $total code objects byte-identical to stage 0"
echo "image run:   $((total - i)) of $total code objects byte-identical to stage 0 (measurement)"
[ "$w" = 0 ] && [ "$c" = 0 ] || { echo "REPRODUCTION_FAILED"; exit 7; }
echo "CAPTURE_OK"
