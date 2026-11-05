(* E2E-20 Wave C: bit-level agreement lemmas for BuriArmBridge.v.
   Plain Coq rewriting (no ssreflect); see BuriArmBridge.v for the toolchain
   and what the bridge establishes.  All lemmas are closed under the global
   context: they are about stdpp bitvectors and the model's AddWithCarry. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmAdds.
Import Defs.
Open Scope Z.

(* mword 64 carries the index Z_idx 64; unify it with 64%N before lia. *)
Ltac zl := change (MachineWord.MachineWord.Z_idx 64) with 64%N in *; lia.

(* ---------------------------------------------------------------- *)
(* The isla trace's values agree with the model's AddWithCarry. *)
Section values.
Context (x0 x1 : mword 64).

Definition isla_sum : bv 64 := bv_extract 0 64 (bv_add (bv_zero_extend 128 x0) (bv_zero_extend 128 x1)).

Lemma uint64 (x : mword 64) : uint x = bv_unsigned x.
Proof.
  unfold uint, MachineWord.MachineWord.word_to_N, get_word.
  rewrite Z2N.id; [done|]. apply (bv_unsigned_in_range 64 x).
Qed.

Lemma isla_sum_model : isla_sum = adds_sum x0 x1.
Proof.
  apply bv_eq. unfold isla_sum.
  rewrite bv_extract_unsigned, bv_add_unsigned, !bv_zero_extend_unsigned by (vm_compute; discriminate).
  transitivity (uint (adds_sum x0 x1)); [|apply uint64].
  rewrite chez_0014_sum, !uint64.
  pose proof (bv_unsigned_in_range 64 x0). pose proof (bv_unsigned_in_range 64 x1).
  unfold bv_modulus in *. rewrite Z.shiftr_0_r.
  rewrite (bv_wrap_small 128); [|unfold bv_modulus; simpl in *; zl].
  reflexivity.
Qed.

Lemma bit1_eq (a b : bv 1) : bv_unsigned a = bv_unsigned b → a = b.
Proof. apply bv_eq. Qed.

Lemma isla_N (r : mword 64) :
  bv_or (bv_and 0 (bv_not 1)) (bv_extract 0 1 (r ≫ bv_extract 0 64 (63 : bv 128))) =
  (vec_of_bits [access_vec_dec r 63] : mword 1).
Proof.
  change (access_vec_dec r 63) with (bitU_of_bool (Z.testbit (bv_unsigned r) 63)).
  apply bit1_eq.
  rewrite bv_or_unsigned, bv_extract_unsigned, bv_shiftr_unsigned.
  change (bv_unsigned (bv_and 0 (bv_not 1) : bv 1)) with 0.
  change (bv_unsigned (bv_extract 0 64 (63 : bv 128))) with 63.
  rewrite Z.lor_0_l, Z.shiftr_0_r.
  assert (Hb : bv_wrap 1 (Z.shiftr (bv_unsigned r) 63) = Z.b2z (Z.testbit (bv_unsigned r) 63)).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 1) with 2.
    rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia. simpl.
    destruct (Z.testbit (bv_unsigned r) 63); reflexivity. }
  rewrite Hb. destruct (Z.testbit (bv_unsigned r) 63); reflexivity.
Qed.

Lemma isla_Z (r : mword 64) :
  (if bool_decide (r = 0%bv) then (1%bv : bv 1) else 0%bv) = (if IsZero r then 'b"1" else 'b"0" : mword 1).
Proof.
  assert (H : IsZero r = bool_decide (r = 0%bv)).
  { unfold IsZero, eq_vec, MachineWord.MachineWord.eqb, get_word.
    apply bool_decide_ext.
    assert (Hz : (zeros 64 : mword 64) = 0%bv) by (apply bv_eq; reflexivity).
    rewrite Hz. reflexivity. }
  rewrite H. destruct (bool_decide (r = 0%bv)); apply bv_eq; reflexivity.
Qed.

Lemma isla_C :
  (if bool_decide (bv_zero_extend 128 (adds_sum x0 x1) =
                    bv_add (bv_zero_extend 128 x0) (bv_zero_extend 128 x1)) then (0%bv : bv 1) else 1%bv) =
  (if Z.eqb (uint (adds_sum x0 x1)) (uint x0 + uint x1 + uint ('b"0" : mword 1))
   then 'b"0" else 'b"1" : mword 1).
Proof.
  change (uint ('b"0" : mword 1)) with 0. rewrite Z.add_0_r, !uint64.
  pose proof (bv_unsigned_in_range 64 x0). pose proof (bv_unsigned_in_range 64 x1).
  unfold bv_modulus in *. simpl in *.
  case_bool_decide as Hd;
    match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) as [He|He] end;
    try (apply bv_eq; reflexivity); exfalso.
  - apply He. apply (f_equal bv_unsigned) in Hd.
    rewrite bv_add_unsigned, !bv_zero_extend_unsigned in Hd by (vm_compute; discriminate).
    rewrite Hd. apply bv_wrap_small. unfold bv_modulus. simpl. zl.
  - apply Hd. apply bv_eq.
    rewrite bv_add_unsigned, !bv_zero_extend_unsigned by (vm_compute; discriminate).
    rewrite He. symmetry. apply bv_wrap_small. unfold bv_modulus. simpl. zl.
Qed.

Lemma isla_V :
  (if bool_decide (bv_sign_extend 128 (adds_sum x0 x1) =
                    bv_add (bv_sign_extend 128 x0) (bv_sign_extend 128 x1)) then (0%bv : bv 1) else 1%bv) =
  (if Z.eqb (sint (adds_sum x0 x1)) (sint x0 + sint x1 + uint ('b"0" : mword 1))
   then 'b"0" else 'b"1" : mword 1).
Proof.
  change (uint ('b"0" : mword 1)) with 0. rewrite Z.add_0_r.
  change (sint (adds_sum x0 x1)) with (bv_signed (adds_sum x0 x1)).
  change (sint x0) with (bv_signed x0). change (sint x1) with (bv_signed x1).
  pose proof (bv_signed_in_range 64 x0 ltac:(done)).
  pose proof (bv_signed_in_range 64 x1 ltac:(done)).
  assert (Hm64 : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  assert (Hm128 : bv_half_modulus 128 = 2 ^ 127) by reflexivity.
  rewrite Hm64 in *.
  assert (Hs : bv_signed (bv_add (bv_sign_extend 128 x0) (bv_sign_extend 128 x1))
               = bv_signed x0 + bv_signed x1).
  { rewrite bv_add_signed, !bv_sign_extend_signed by (vm_compute; discriminate).
    apply bv_swrap_small. rewrite Hm128. zl. }
  case_bool_decide as Hd;
    match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) as [He|He] end;
    try (apply bv_eq; reflexivity); exfalso.
  - apply He. apply (f_equal bv_signed) in Hd.
    rewrite bv_sign_extend_signed in Hd by (vm_compute; discriminate). rewrite Hd. exact Hs.
  - apply Hd. apply bv_eq_signed. rewrite bv_sign_extend_signed by (vm_compute; discriminate). rewrite He. done.
Qed.
End values.

Print Assumptions isla_sum_model.
Print Assumptions isla_N.
Print Assumptions isla_Z.
Print Assumptions isla_C.
Print Assumptions isla_V.
