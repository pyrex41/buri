#!/bin/bash
# Opt-in E2E-20 gate: check ports/arm/coq/BuriArmAdds.v against the
# authoritative sail-arm Armv9.4-A Coq model.  NOT part of `make prove`: the
# model needs a separate toolchain (docs/ARM-FOUNDATION.md section 10) and
# 24 min / 6.4 GB to elaborate once.  Acceptance is decided by coqc; this
# script only binds inputs (hashes, captured bytes) and orchestrates.
#
# What a pass trusts: the Sail-to-Coq translation of sail-arm 7d058164 (the Coq
# text is the model), coq-sail-stdpp 0.19, nixpkgs Coq 8.18.0 + stdpp 1.10.0,
# and the three Coq-stdlib Reals axioms that the model's decoder depends on
# (listed in EXPECT_DECODER_AXIOMS below; no axiom is added by Buri).
#
#   SAIL_ARM_COQ   directory holding armv9_types.vo, arm_extras.vo, armv9.vo
#                  compiled from sail-arm 7d058164 arm-v9.4-a/snapshots/coq
#                  with `-R . SailArm` (ports/arm/coq/build-*.sh)
#   COQ_SAIL       coq-sail tag 0.19 (6918e8f3) src-stdpp, compiled
#   COQ818         nixpkgs coq-8.18.0 store path   (default below)
#   STDPP818       nixpkgs coq8.18-stdpp-1.10.0 store path (default below)
set -euo pipefail
cd "$(dirname "$0")/.."
: "${SAIL_ARM_COQ:?Set SAIL_ARM_COQ to the compiled sail-arm Coq model directory}"
: "${COQ_SAIL:?Set COQ_SAIL to the compiled coq-sail 0.19 src-stdpp directory}"
: "${COQ818:=/nix/store/z93aiwvyich2swj7qx9ahccwj15hzx8y-coq-8.18.0}"
: "${STDPP818:=/nix/store/xz8bq0nyg9j6b37pja9qxvbj4w15wmqf-coq8.18-stdpp-1.10.0}"
export PATH="$COQ818/bin:$PATH"
export COQPATH="$STDPP818/lib/coq/8.18/user-contrib"
coqc --version | grep -q 'version 8.18.0' || { echo 'Need Coq 8.18.0' >&2; exit 1; }

# 1. The model text is the pinned snapshot.
check_sha() { echo "$1  $2" | sha256sum -c --quiet - || { echo "Unexpected $2" >&2; exit 1; }; }
check_sha 5169ce7f4d10ab1a37bb77dd6a41114838c65fc0ceea4e9ef9cd1e73d8d1e68a "$SAIL_ARM_COQ/armv9.v"
check_sha 3586eb0f632fb642a39bbe5a526b2ffb34267725440fc9e9981e61a6de31a998 "$SAIL_ARM_COQ/armv9_types.v"
check_sha a82f366aadebfd12aaef4f7e6cdb5088c40b7a90ad4781e03b7baff9991b278c "$SAIL_ARM_COQ/arm_extras.v"
for v in armv9_types arm_extras armv9; do
  [ "$SAIL_ARM_COQ/$v.vo" -nt "$SAIL_ARM_COQ/$v.v" ] || { echo "Stale or missing $v.vo" >&2; exit 1; }
done

# 2. The word in the theorem is the captured byte sequence (Chez +0x14).
bin=ports/arm/chez/chez1030-buri-arm-add.bin
check_sha "$(grep ' ./chez/chez1030-buri-arm-add.bin$' ports/arm/SHA256SUMS | cut -d' ' -f1)" "$bin"
b=($(od -An -tx1 -j 20 -N 4 "$bin"))
word=$(printf '%s%s%s%s' "${b[3]}" "${b[2]}" "${b[1]}" "${b[0]}" | tr a-f A-F)
line="Definition chez_word_0014 : mword 32 := Ox\"$word\"."
grep -qxF "$line" ports/arm/coq/BuriArmAdds.v || { echo "Word mismatch: captured $word" >&2; exit 1; }
echo "Captured word at +0x14: 0x$word"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
ulimit -s unlimited
Q=(-Q "$COQ_SAIL" SailStdpp -R "$SAIL_ARM_COQ" SailArm)

# 3. Check the proofs.
cp ports/arm/coq/BuriArmAdds.v "$tmp/BuriArmAdds.v"
(cd "$tmp" && coqc "${Q[@]}" -Q . BuriArm BuriArmAdds.v) > "$tmp/out.log" 2>&1 \
  || { cat "$tmp/out.log" >&2; exit 1; }

# 4. Assumption audit: decoder statements depend exactly on the model's own
#    Reals axioms; the execute equation and bitvector lemma are closed.
python3 - "$tmp/out.log" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
blocks = re.split(r'\n(?=Axioms:|Closed under the global context)', text)
audit = [b for b in blocks if b.startswith(('Axioms:', 'Closed under'))]
expect_decoder = {'ClassicalDedekindReals.sig_not_dec',
                  'ClassicalDedekindReals.sig_forall_dec',
                  'FunctionalExtensionality.functional_extensionality_dep'}
names = lambda b: set(re.findall(r'^([A-Za-z_][\w.]*) :', b, re.M)) | \
                  set(re.findall(r'^([A-Za-z_][\w.]*)$', b, re.M)) - {'Axioms:'}
got = [('closed' if b.startswith('Closed') else frozenset(names(b))) for b in audit]
want = [frozenset(expect_decoder), 'closed', frozenset(expect_decoder), 'closed', frozenset(expect_decoder)]
if got != want:
    print('Assumption audit mismatch:', got, file=sys.stderr); sys.exit(1)
print('Assumption audit: decoder theorems use only the model\'s Reals axioms; execute/sum closed')
EOF

# 5. A modified word must be rejected (the proof is about these bytes).
sed 's/Ox"AB010017"/Ox"AB010018"/' ports/arm/coq/BuriArmAdds.v > "$tmp/BuriArmAddsMutant.v"
if (cd "$tmp" && coqc "${Q[@]}" -Q . BuriArm BuriArmAddsMutant.v) > "$tmp/mut.log" 2>&1; then
  echo 'Incorrectly admitted modified word 0xab010018' >&2; exit 1
fi
# The rejection must come from the decode theorem's proof, not from parsing.
grep -A3 '^Error' "$tmp/mut.log" | head -4 >&2
grep -q 'Unable to unify' "$tmp/mut.log" || { echo 'Mutant failed for another reason' >&2; exit 1; }
echo 'Rejected modified word 0xab010018 (Rd=24)'
echo 'BURI_ARM_CHECK_OK'
