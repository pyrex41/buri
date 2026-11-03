(* E2E-20 Wave D: bit-level agreement lemmas for the cmp (+0x00) and
   tst (+0x0c) bridges in BuriArmFastPathBridge.v.  Plain Coq; every lemma is
   closed under the global context (stdpp bitvectors and the model's
   AddWithCarry / IsZeroBit).  NOT a scripts/prove module. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmBridgeValues BuriArm.BuriArmFastPath.
Import Defs.
Open Scope Z.

Ltac zl := change (MachineWord.MachineWord.Z_idx 64) with 64%N in *; lia.

Lemma awc_sum (a b : mword 64) (c : mword 1) :
  uint (fst (AddWithCarry a b c)) = (uint a + uint b + uint c) mod 2 ^ 64.
Proof.
  unfold AddWithCarry. cbn [fst].
  generalize (uint a + uint b + uint c) as s. intros s.
  unfold integer_subrange. rewrite get_slice_int_eta. unfold get_slice_int'.
  destruct (sumbool_of_bool _) as [h|h]; [|vm_compute in h; discriminate h].
  rewrite !(autocast_eq _ eq_refl), !cast_Z_refl.
  unfold subrange_vec_dec, to_word_idx.
  rewrite (autocast_eq _ eq_refl), cast_Z_refl, MachineWord.MachineWord.cast_idx_refl.
  unfold uint, MachineWord.MachineWord.word_to_N, MachineWord.MachineWord.slice, get_word,
    to_word, mword_of_int, MachineWord.MachineWord.Z_to_word.
  repeat match goal with |- context [Z.to_N ?e] =>
    lazymatch e with bv_unsigned _ => fail | _ =>
    let v := eval vm_compute in (Z.to_N e) in change (Z.to_N e) with v end end.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Zmod_mod. reflexivity.
Qed.

Section cmp.
Context (x : mword 64) (k2 k1 s2 : bv 128).
Hypothesis Hk2 : bv_unsigned k2 = 18446744073709551613.
Hypothesis Hk1 : bv_unsigned k1 = 1.
Hypothesis Hs2 : bv_signed s2 = -3.
Let y : mword 64 := not_vec (Ox"0000000000000002").
Let R := fst (cmp_result x).

Lemma uint_y : uint y = 18446744073709551613.
Proof. vm_compute. reflexivity. Qed.
Lemma sint_y : sint y = -3.
Proof. vm_compute. reflexivity. Qed.
Lemma uint_1 : uint ('b"1" : mword 1) = 1.
Proof. reflexivity. Qed.

Lemma S_unsigned : bv_unsigned (bv_zero_extend 128 x + k2 + k1)%bv = uint x + 18446744073709551613 + 1.
Proof.
  rewrite !bv_add_unsigned, bv_zero_extend_unsigned by (vm_compute; discriminate).
  rewrite Hk2, Hk1. rewrite <- uint64.
  pose proof (bv_unsigned_in_range 64 x) as Hx. rewrite <- uint64 in Hx. unfold bv_modulus in Hx.
  rewrite (bv_wrap_small 128 (uint x + _)); [|unfold bv_modulus; simpl in *; zl].
  apply bv_wrap_small. unfold bv_modulus. simpl in *. zl.
Qed.

Lemma cmp_sum_isla : bv_extract 0 64 (bv_zero_extend 128 x + k2 + k1)%bv = R.
Proof.
  apply bv_eq. rewrite bv_extract_unsigned, S_unsigned, Z.shiftr_0_r.
  transitivity (uint R); [|apply uint64].
  unfold R, cmp_result. rewrite awc_sum. fold y. rewrite uint_y, uint_1.
  reflexivity.
Qed.

Lemma cmp_C_isla :
  (if bool_decide (bv_zero_extend 128 R = (bv_zero_extend 128 x + k2 + k1)%bv) then (0%bv : bv 1) else 1%bv) =
  (if Z.eqb (uint R) (uint x + uint y + uint ('b"1" : mword 1)) then 'b"0" else 'b"1" : mword 1).
Proof.
  rewrite uint_y, uint_1.
  pose proof (bv_unsigned_in_range 64 x) as Hx. rewrite <- uint64 in Hx. unfold bv_modulus in Hx.
  case_bool_decide as Hd;
    match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) as [He|He] end;
    try (apply bv_eq; reflexivity); exfalso.
  - apply He. apply (f_equal bv_unsigned) in Hd.
    rewrite bv_zero_extend_unsigned, S_unsigned in Hd by (vm_compute; discriminate).
    rewrite <- uint64 in Hd. exact Hd.
  - apply Hd. apply bv_eq.
    rewrite bv_zero_extend_unsigned, S_unsigned by (vm_compute; discriminate).
    rewrite <- uint64. exact He.
Qed.

Lemma cmp_V_isla :
  (if bool_decide (bv_sign_extend 128 R = (bv_sign_extend 128 x + s2 + k1)%bv) then (0%bv : bv 1) else 1%bv) =
  (if Z.eqb (sint R) (sint x + sint y + uint ('b"1" : mword 1)) then 'b"0" else 'b"1" : mword 1).
Proof.
  rewrite sint_y, uint_1.
  change (sint R) with (bv_signed R). change (sint x) with (bv_signed x).
  pose proof (bv_signed_in_range 64 x ltac:(done)) as Hx.
  assert (Hm64 : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  assert (Hm128 : bv_half_modulus 128 = 2 ^ 127) by reflexivity.
  rewrite Hm64 in Hx.
  assert (Hk1s : bv_signed k1 = 1).
  { unfold bv_signed, bv_swrap. rewrite Hk1. reflexivity. }
  assert (Hs : bv_signed (bv_sign_extend 128 x + s2 + k1)%bv = bv_signed x + -3 + 1).
  { rewrite !bv_add_signed, bv_sign_extend_signed by (vm_compute; discriminate).
    rewrite Hs2, Hk1s.
    rewrite (bv_swrap_small 128 (bv_signed x + -3)); [|rewrite Hm128; zl].
    apply bv_swrap_small. rewrite Hm128. zl. }
  case_bool_decide as Hd;
    match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) as [He|He] end;
    try (apply bv_eq; reflexivity); exfalso.
  - apply He. apply (f_equal bv_signed) in Hd.
    rewrite bv_sign_extend_signed in Hd by (vm_compute; discriminate). rewrite Hd. exact Hs.
  - apply Hd. apply bv_eq_signed. rewrite bv_sign_extend_signed by (vm_compute; discriminate).
    rewrite He, Hs. reflexivity.
Qed.
End cmp.

(* tst: the model's flags for ANDS are N = result[63], Z = IsZeroBit, C = V = 0. *)
Lemma IsZero_bool (r : mword 64) : IsZero r = bool_decide (r = 0%bv).
Proof.
  unfold IsZero, eq_vec, MachineWord.MachineWord.eqb, get_word.
  apply bool_decide_ext.
  assert (Hz : (zeros 64 : mword 64) = 0%bv) by (apply bv_eq; reflexivity).
  rewrite Hz. reflexivity.
Qed.

Lemma tst_N_isla (r : mword 64) (b0 : bv 1) (s : bv 64) :
  bv_unsigned b0 = 0 -> bv_unsigned s = 63 ->
  bv_or b0 (bv_extract 0 1 (bv_shiftr r s)) = (vec_of_bits [access_vec_dec r 63] : mword 1).
Proof.
  intros Hb0 Hs.
  change (access_vec_dec r 63) with (bitU_of_bool (Z.testbit (bv_unsigned r) 63)).
  apply bit1_eq.
  rewrite bv_or_unsigned, bv_extract_unsigned, bv_shiftr_unsigned, Hb0.
  match goal with |- context [Z.shiftr (bv_unsigned r) ?t] => replace t with 63 by (exact (eq_sym Hs)) end.
  rewrite Z.lor_0_l, Z.shiftr_0_r.
  assert (Hb : bv_wrap 1 (Z.shiftr (bv_unsigned r) 63) = Z.b2z (Z.testbit (bv_unsigned r) 63)).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 1) with 2.
    rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia. simpl.
    destruct (Z.testbit (bv_unsigned r) 63); reflexivity. }
  rewrite Hb. destruct (Z.testbit (bv_unsigned r) 63); reflexivity.
Qed.

Section tst_bv.
Transparent Z_to_bv bv_and.
Lemma tst_result_bv (x : mword 64) : tst_result x = bv_and x (BV 64 7).
Proof. apply bv_eq. reflexivity. Qed.
End tst_bv.

Print Assumptions awc_sum.
Print Assumptions cmp_sum_isla.
Print Assumptions cmp_C_isla.
Print Assumptions cmp_V_isla.
Print Assumptions IsZero_bool.
Print Assumptions tst_N_isla.
Print Assumptions tst_result_bv.
