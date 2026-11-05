#!/bin/bash
# Shows each gate in check.sh fires. Each case runs check.sh from a modified copy of the spike.
here=$(cd "$(dirname "$0")" && pwd)
try() { # name, expected exit, sed expr, file
  t=$(mktemp -d); cp -a "$here"/. "$t"/
  sed -i "$3" "$t/$4"
  SKIP_CAPTURE=1 bash "$t/check.sh" > /tmp/gt.log 2>&1; rc=$?
  [ "$rc" = "$2" ] && echo "fired $1 exit=$rc: $(grep -m1 FAIL /tmp/gt.log | cut -c1-70)" || { echo "GATE_DID_NOT_FIRE $1 exit=$rc wanted=$2"; tail -3 /tmp/gt.log | cut -c1-160; }
  rm -rf "$t"
}
try wrong-bytes-hash 2 's/sha256 9c5e/sha256 0c5e/' coq/SliceCode.v
try wrong-helper-symbol 3 's/Definition H_ALLOC : word := Z_to_bv 64 0x27860/Definition H_ALLOC : word := Z_to_bv 64 0x27864/' coq/SliceProof.v
try unjustified-axiom 6 's/^Lemma tag_low : forall x : word, tag3 x = TAG_PAIR -> (3 <= bv_unsigned x)%Z\./Axiom tag_low : forall x : word, tag3 x = TAG_PAIR -> (3 <= bv_unsigned x)%Z.\nLemma tag_low_unused : True./; s/^  intros x H\. unfold tag3, TAG_PAIR in H\./  exact I. Qed. Lemma tag_low_rest : forall x : word, tag3 x = TAG_PAIR -> (3 <= bv_unsigned x)%Z. Proof. intros x H. unfold tag3, TAG_PAIR in H./' coq/SliceProof.v
try admitted-proof 7 's/^Print Assumptions slice_refines\./Lemma later : False. Admitted./' coq/SliceProof.v
