(* E2E-21: Chez Scheme 10.3.0 tarm64le machine words and fixnums.

   Every constant comes from ChezLayout (generated from pinned sources by
   scripts/package-repr-layout.py). This module uses only the Coq standard
   library so that the same source also compiles in the separate Coq 8.19
   Islaris toolchain (ports/arm/islaris/check-islaris-shen.sh), where it links
   the Islaris fast-path theorem to Shen integers.

   Evidence kinds: `chez_fixnum_layout` and `chez_word_layout` are ground
   derivations (closed computations on the pinned constants); every other
   lemma is a universally quantified theorem. *)
From Coq Require Import ZArith Lia.
From Buri Require Import ChezLayout.
Open Scope Z_scope.
Module ChezWord.
Import ChezLayout.ChezLayout.

(* 64-bit words as integers in [0, 2^64); swrap is the two's-complement
   reading, written exactly like stdpp's bv_swrap 64. *)
Definition modulus : Z := 2 ^ ptr_bits.
Definition half : Z := 2 ^ (ptr_bits - 1).
Definition word_ok (w : Z) : Prop := 0 <= w < modulus.
Definition wrap (z : Z) : Z := z mod modulus.
Definition swrap (z : Z) : Z := (z + half) mod modulus - half.

(* Chez fixnums: a fixnum z is the word z * fixnum_factor (shift by
   fixnum_offset), primary tag type_fixnum. *)
Definition fx_range (z : Z) : Prop := most_negative_fixnum <= z <= most_positive_fixnum.
Definition fx_rangeb (z : Z) : bool := (Z.leb most_negative_fixnum z && Z.leb z most_positive_fixnum)%bool.
Definition fx_enc (z : Z) : Z := wrap (z * fixnum_factor).
Definition fx_dec (w : Z) : Z := swrap w / fixnum_factor.   (* arithmetic shift right *)
Definition fixnum_tagged (w : Z) : Prop := Z.land w mask_fixnum = type_fixnum.

(* Ground derivation: the pinned fixnum constants are mutually consistent
   and agree with the cmacros.ss literals and arm64.def. *)
Lemma chez_fixnum_layout :
  ptr_bits = 64 /\ def_ptr_bits = ptr_bits /\ fixnum_offset = 3 /\
  fixnum_bits + fixnum_offset = ptr_bits /\ fixnum_factor = 2 ^ fixnum_offset /\
  mask_fixnum = fixnum_factor - 1 /\ mask_fixnum = typemod - 1 /\ type_fixnum = 0 /\
  cm_type_fixnum = type_fixnum /\ typemod = cm_typemod /\ typemod = 2 ^ primary_type_bits /\
  most_positive_fixnum = 2 ^ (fixnum_bits - 1) - 1 /\
  most_negative_fixnum = - 2 ^ (fixnum_bits - 1).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma chez_word_layout : modulus = 18446744073709551616 /\ half = 9223372036854775808 /\
  fixnum_factor = 8 /\ mask_fixnum = 7 /\
  most_positive_fixnum = 1152921504606846975 /\ most_negative_fixnum = -1152921504606846976.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fx_rangeb_spec : forall z, fx_rangeb z = true <-> fx_range z.
Proof.
  intro z; unfold fx_rangeb, fx_range; rewrite Bool.andb_true_iff, !Z.leb_le; tauto.
Qed.

Ltac chez_consts :=
  destruct chez_word_layout as (HM & HH & HF & HK & HP & HN);
  unfold fx_range, fixnum_tagged, word_ok, fx_enc, fx_dec, wrap, swrap in *;
  rewrite ?HM, ?HH, ?HF, ?HK, ?HP, ?HN in *.

Lemma wrap_ok : forall z, word_ok (wrap z).
Proof.
  intro z; destruct chez_word_layout as (HM & _); unfold word_ok, wrap; rewrite HM.
  apply Z.mod_pos_bound; lia.
Qed.

Lemma swrap_small : forall z, - half <= z < half -> swrap (wrap z) = z.
Proof.
  intros z H; destruct chez_word_layout as (HM & HH & _).
  unfold swrap, wrap; rewrite HM, HH in *.
  rewrite Zplus_mod_idemp_l, Z.mod_small; lia.
Qed.

Lemma swrap_wrap : forall z, swrap (wrap z) = swrap z.
Proof. intro z; unfold swrap, wrap; rewrite Zplus_mod_idemp_l; reflexivity. Qed.

Lemma swrap_range : forall z, - half <= swrap z < half.
Proof.
  intro z; destruct chez_word_layout as (HM & HH & _); unfold swrap; rewrite HM, HH.
  pose proof (Z.mod_pos_bound (z + 9223372036854775808) (18446744073709551616) ltac:(lia)); lia.
Qed.

(* Every fixnum encoding is a word with fixnum tag. *)
Theorem fx_enc_word : forall z, word_ok (fx_enc z).
Proof. intro z; apply wrap_ok. Qed.

Theorem fx_enc_tagged : forall z, fixnum_tagged (fx_enc z).
Proof.
  intro z; chez_consts.
  change 7 with (Z.ones 3); rewrite Z.land_ones by lia.
  rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 2305843009213693952; reflexivity].
  rewrite Z.mod_mul by lia; reflexivity.
Qed.

(* Round trip and injectivity on the fixnum range. *)
Theorem fx_dec_enc : forall z, fx_range z -> fx_dec (fx_enc z) = z.
Proof.
  intros z H; unfold fx_dec, fx_enc.
  rewrite swrap_small; destruct chez_word_layout as (_ & HH & HF & _ & HP & HN);
    unfold fx_range in H; rewrite HF in *; rewrite ?HH, ?HP, ?HN in *.
  - apply Z.div_mul; lia.
  - lia.
Qed.

Theorem fx_enc_inj : forall x y, fx_range x -> fx_range y -> fx_enc x = fx_enc y -> x = y.
Proof. intros x y Hx Hy E; rewrite <- (fx_dec_enc x Hx), <- (fx_dec_enc y Hy), E; reflexivity. Qed.

(* Every fixnum-tagged word is the encoding of exactly one fixnum. *)
Theorem fx_enc_dec : forall w, word_ok w -> fixnum_tagged w ->
  fx_range (fx_dec w) /\ fx_enc (fx_dec w) = w.
Proof.
  intros w Hw Ht.
  assert (Hm : w mod 8 = 0).
  { destruct chez_word_layout as (_ & _ & _ & HK & _); unfold fixnum_tagged in Ht; rewrite HK in Ht.
    change 7 with (Z.ones 3) in Ht; rewrite Z.land_ones in Ht by lia; exact Ht. }
  pose proof (swrap_range w) as R.
  assert (Hs : (swrap w) mod 8 = 0).
  { destruct chez_word_layout as (HM & HH & _); unfold swrap; rewrite HM, HH.
    rewrite Zminus_mod, <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 2305843009213693952; reflexivity].
    rewrite Zplus_mod, Hm; reflexivity. }
  assert (He : swrap w = 8 * (swrap w / 8)) by (apply Z_div_exact_2; lia).
  destruct chez_word_layout as (HM & HH & HF & _ & HP & HN).
  unfold fx_dec, fx_range, fx_enc; rewrite HF, HP, HN; rewrite HH in R.
  split; [lia|].
  rewrite Z.mul_comm, <- He.
  unfold wrap, swrap; rewrite HM, HH; unfold word_ok in Hw; rewrite HM in Hw.
  destruct (Z.lt_ge_cases w (9223372036854775808)).
  - rewrite (Z.mod_small (w + 9223372036854775808)) by lia. rewrite Z.mod_small; lia.
  - rewrite <- (Z.mod_unique (w + 9223372036854775808) 18446744073709551616 1
               (w + 9223372036854775808 - 18446744073709551616)) by lia.
    symmetry; apply (Z.mod_unique _ _ (-1)); lia.
Qed.

(* Signed reading of a fixnum word is the shifted integer. *)
Theorem fx_enc_signed : forall z, fx_range z -> swrap (fx_enc z) = z * 8.
Proof.
  intros z H; unfold fx_enc; destruct chez_word_layout as (_ & HH & HF & _ & HP & HN).
  rewrite HF; apply swrap_small; unfold fx_range in H; rewrite HH; rewrite HP, HN in H; lia.
Qed.

(* Tagged addition: the wrapped sum of two fixnum words is the fixnum word of
   the sum (for all integers; meaningful when the sum is in range). *)
Theorem fx_add_wrap : forall x y, wrap (fx_enc x + fx_enc y) = fx_enc (x + y).
Proof.
  intros x y; unfold fx_enc, wrap; rewrite <- Zplus_mod; f_equal; ring.
Qed.

(* The 64-bit signed addition of two fixnum words does not overflow exactly
   when the Shen sum stays in the fixnum range: the ADDS/BVS check of the
   Chez fast path is a fixnum-range test. *)
Theorem fx_add_no_overflow_iff : forall x y, fx_range x -> fx_range y ->
  (- half <= swrap (fx_enc x) + swrap (fx_enc y) < half <-> fx_range (x + y)).
Proof.
  intros x y Hx Hy; rewrite (fx_enc_signed x Hx), (fx_enc_signed y Hy).
  destruct chez_word_layout as (_ & HH & _ & _ & HP & HN).
  unfold fx_range; rewrite HH, HP, HN; lia.
Qed.

Theorem fx_add_in_range : forall x y, fx_range x -> fx_range y -> fx_range (x + y) ->
  swrap (fx_enc x) + swrap (fx_enc y) = swrap (fx_enc (x + y)).
Proof.
  intros x y Hx Hy Hs; rewrite !fx_enc_signed by assumption; ring.
Qed.

(* Tag test of the fast path: (a | b) & mask_fixnum = 0 iff both are
   fixnum-tagged. *)
Theorem tag_or_iff : forall a b,
  Z.land (Z.lor a b) mask_fixnum = 0 <-> fixnum_tagged a /\ fixnum_tagged b.
Proof.
  intros a b; destruct chez_fixnum_layout as (_ & _ & _ & _ & _ & _ & _ & HT & _).
  unfold fixnum_tagged; rewrite HT, Z.land_lor_distr_l; split.
  - intro H; apply Z.lor_eq_0_iff in H; exact H.
  - intros [A B]; rewrite A, B; reflexivity.
Qed.

Theorem fx_or_tag : forall x y, Z.land (Z.lor (fx_enc x) (fx_enc y)) mask_fixnum = 0.
Proof. intros; apply tag_or_iff; split; apply fx_enc_tagged. Qed.

End ChezWord.
