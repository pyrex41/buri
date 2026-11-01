#!/bin/sh
# Opt-in native gate for the Shen-CL lane. It orchestrates capture and native
# samples; every acceptance decision is a Rocq computation (admission) or a
# native sample assertion. `make prove` checks the stored captures without it.
set -eu
cd "$(dirname "$0")/.."
: "${SHEN_CL_SOURCE:?Set SHEN_CL_SOURCE to the Shen-CL checkout}"
: "${SBCL:=sbcl}"
: "${COQC:=coqc}"
expected=4844072dde0208c3e4b99dcbfea58e4fdfd812e8
compiler_blob=2d624377c02030f9513769f7bad11e84330b8c5a
actual=$(git -C "$SHEN_CL_SOURCE" rev-parse HEAD)
[ "$actual" = "$expected" ] || { echo "Wrong Shen-CL revision: $actual" >&2; exit 1; }
git -C "$SHEN_CL_SOURCE" diff --quiet HEAD -- src/primitives.lsp src/compiler.shen || { echo 'Modified port source' >&2; exit 1; }
blob=$(git -C "$SHEN_CL_SOURCE" rev-parse HEAD:src/compiler.shen)
[ "$blob" = "$compiler_blob" ] || { echo "Unexpected compiler.shen blob: $blob" >&2; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

# 1. Strict Boolean guard (src/primitives.lsp shen-cl.true?).
cp rocq/CLPortGuard.v "$tmp/CLPortGuard.v"
"$COQC" -Q "$tmp" Buri "$tmp/CLPortGuard.v"
"$SBCL" --script ports/shen-cl-capture.lisp "$SHEN_CL_SOURCE/src/primitives.lsp" "$tmp/CLPortCapture.v"
cmp rocq/CLPortCapture.v "$tmp/CLPortCapture.v"
cmp ports/shen-cl-guard.sexp "$tmp/CLPortCapture.sexp"
"$COQC" -Q "$tmp" Buri "$tmp/CLPortCapture.v"
for mutation in swap host-truthiness changed-message; do
  "$SBCL" --script ports/shen-cl-capture.lisp "$SHEN_CL_SOURCE/src/primitives.lsp" "$tmp/CLPortMutant.v" "$mutation"
  if "$COQC" -Q "$tmp" Buri "$tmp/CLPortMutant.v" >"$tmp/rejection.log" 2>&1; then
    echo "Incorrectly admitted $mutation" >&2; exit 1
  fi
  grep -q 'Unable to unify "true" with "false"' "$tmp/rejection.log" || { cat "$tmp/rejection.log" >&2; exit 1; }
  echo "Rejected modified capture: $mutation"
done

# 2. Conditional lowering (src/compiler.shen emit-if, optimise-boolean-check).
cp rocq/CLLowering.v "$tmp/CLLowering.v"
"$COQC" -Q "$tmp" Buri "$tmp/CLLowering.v"
capture() {
  scripts/shen -l shen/cl-lowering-capture.shen \
    -e "(buri.cll-capture \"$SHEN_CL_SOURCE/src/compiler.shen\" \"$blob\" \"$1\" $2)" >"$tmp/capture.log" 2>&1
  grep -qx captured "$tmp/capture.log" || { cat "$tmp/capture.log" >&2; exit 1; }
}
capture "$tmp/CLLoweringCapture.v" none
cmp rocq/CLLoweringCapture.v "$tmp/CLLoweringCapture.v"
"$COQC" -Q "$tmp" Buri "$tmp/CLLoweringCapture.v"
for mutation in dropped-guard cl-truthiness swapped-branches eq-for-equal; do
  capture "$tmp/CLLoweringMutant.v" "$mutation"
  if cmp -s "$tmp/CLLoweringMutant.v" "$tmp/CLLoweringCapture.v"; then
    echo "Mutation did not change the capture: $mutation" >&2; exit 1
  fi
  if "$COQC" -Q "$tmp" Buri "$tmp/CLLoweringMutant.v" >"$tmp/rejection.log" 2>&1; then
    echo "Incorrectly admitted $mutation" >&2; exit 1
  fi
  grep -q 'Unable to unify "true" with "false"' "$tmp/rejection.log" || { cat "$tmp/rejection.log" >&2; exit 1; }
  echo "Rejected modified lowering capture: $mutation"
done

# 3. Sampled agreement: run the actual compiler.shen on the Shen host and let
#    Rocq compare its outputs with the interpretation of the admitted capture.
scripts/shen -l shen/cl-lowering-capture.shen -e "(load \"$SHEN_CL_SOURCE/src/compiler.shen\")" \
  -l shen/cl-lowering-samples.shen -e "(buri.cll-samples \"$tmp/CLLoweringSamples.v\")" >"$tmp/samples.log" 2>&1
grep -qx sampled "$tmp/samples.log" || { cat "$tmp/samples.log" >&2; exit 1; }
cmp rocq/CLLoweringSamples.v "$tmp/CLLoweringSamples.v"
"$COQC" -Q "$tmp" Buri "$tmp/CLLoweringSamples.v"
echo "CL lowering: sampled agreement checked by Rocq ($(grep -c '^Example' "$tmp/CLLoweringSamples.v") samples)."

# 4. Native SBCL samples of the named primitive contracts and Shen macros.
"$SBCL" --script ports/shen-cl-contracts.lisp "$SHEN_CL_SOURCE/src/primitives.lsp"
