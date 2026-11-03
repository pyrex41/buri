(* E2E-21 (CL side): SBCL 2.6.8 arm64 machine words, lowtags and fixnums.

   Every constant comes from SbclLayout (generated from the pinned SBCL
   sources and the image capture by scripts/package-repr-layout.py).
   SBCL arm64 fixnums carry one tag bit: a fixnum z is the word 2z mod 2^64
   (n-fixnum-tag-bits 1, fixnum-tag-mask 1), so the even lowtags 0,2,...,14
   are all fixnum lowtags and the fast-path tag test is (a|b)&1 = 0, unlike
   the Chez test (a|b)&7 = 0 (ChezWord).

   Evidence kinds: [sbcl_word_layout] is a ground derivation (a closed
   computation on the pinned constants); every other lemma is a universally
   quantified theorem. Uses only the Coq standard library. *)
From Coq Require Import ZArith Lia.
From Buri Require Import SbclLayout.
Open Scope Z_scope.
Module SbclWord.
Import SbclLayout.SbclLayout.

Definition modulus : Z := 2 ^ img_n_word_bits.
Definition half : Z := 2 ^ (img_n_word_bits - 1).
Definition word_ok (w : Z) : Prop := 0 <= w < modulus.
Definition wrap (z : Z) : Z := z mod modulus.
Definition swrap (z : Z) : Z := (z + half) mod modulus - half.
Definition fixnum_factor : Z := 2 ^ img_n_fixnum_tag_bits.
Definition lowtag (w : Z) : Z := Z.land w img_lowtag_mask.

Definition fx_range (z : Z) : Prop := img_most_negative_fixnum <= z <= img_most_positive_fixnum.
Definition fx_rangeb (z : Z) : bool :=
  (Z.leb img_most_negative_fixnum z && Z.leb z img_most_positive_fixnum)%bool.
Definition fx_enc (z : Z) : Z := wrap (z * fixnum_factor).
Definition fx_dec (w : Z) : Z := swrap w / fixnum_factor.   (* ASR #1 *)
Definition fixnum_tagged (w : Z) : Prop := Z.land w img_fixnum_tag_mask = 0.

(* Ground derivation: the pinned word and fixnum constants. *)
Lemma sbcl_word_layout :
  img_n_word_bits = 64 /\ modulus = 18446744073709551616 /\ half = 9223372036854775808 /\
  img_n_fixnum_tag_bits = 1 /\ fixnum_factor = 2 /\ img_fixnum_tag_mask = 1 /\
  img_fixnum_tag_mask = fixnum_factor - 1 /\ img_n_fixnum_bits + img_n_fixnum_tag_bits = img_n_word_bits /\
  img_lowtag_mask = 15 /\ img_n_lowtag_bits = 4 /\
  img_most_positive_fixnum = 4611686018427387903 /\ img_most_negative_fixnum = -4611686018427387904 /\
  img_most_positive_fixnum = 2 ^ (img_n_fixnum_bits - 1) - 1 /\
  img_most_negative_fixnum = - 2 ^ (img_n_fixnum_bits - 1) /\
  src_n_word_bits = img_n_word_bits /\ src_n_lowtag_bits = img_n_lowtag_bits.
Proof. vm_compute. repeat split; reflexivity. Qed.

Ltac consts :=
  destruct sbcl_word_layout as (HB & HM & HH & HT & HF & HK & _ & _ & HL & _ & HP & HN & _);
  unfold fx_range, fixnum_tagged, word_ok, fx_enc, fx_dec, wrap, swrap, lowtag in *;
  rewrite ?HM, ?HH, ?HF, ?HK, ?HP, ?HN, ?HL in *.

Lemma fx_rangeb_spec : forall z, fx_rangeb z = true <-> fx_range z.
Proof. intro z; unfold fx_rangeb, fx_range; rewrite Bool.andb_true_iff, !Z.leb_le; tauto. Qed.

Lemma wrap_ok : forall z, word_ok (wrap z).
Proof. intro z; consts. apply Z.mod_pos_bound; lia. Qed.

Lemma swrap_small : forall z, - half <= z < half -> swrap (wrap z) = z.
Proof.
  intros z H; consts.
  rewrite Zplus_mod_idemp_l, Z.mod_small; lia.
Qed.

Lemma swrap_range : forall z, - half <= swrap z < half.
Proof.
  intro z; consts.
  pose proof (Z.mod_pos_bound (z + 9223372036854775808) 18446744073709551616 ltac:(lia)); lia.
Qed.

Theorem fx_enc_word : forall z, word_ok (fx_enc z).
Proof. intro z; apply wrap_ok. Qed.

(* Every fixnum encoding is even: its lowtag is a fixnum lowtag. *)
Theorem fx_enc_tagged : forall z, fixnum_tagged (fx_enc z).
Proof.
  intro z; consts.
  change 1 with (Z.ones 1); rewrite Z.land_ones by lia.
  rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 9223372036854775808; reflexivity].
  rewrite Z.mod_mul by lia; reflexivity.
Qed.

Theorem fixnum_lowtag_even : forall w, fixnum_tagged w <-> Z.testbit w 0 = false.
Proof.
  intro w; unfold fixnum_tagged. destruct sbcl_word_layout as (_ & _ & _ & _ & _ & HK & _); rewrite HK.
  change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  rewrite Z.testbit_false by lia. rewrite Z.div_1_r. change (2 ^ 1) with 2. tauto.
Qed.

Theorem fx_enc_even : forall z, Z.testbit (fx_enc z) 0 = false.
Proof. intro z; apply fixnum_lowtag_even, fx_enc_tagged. Qed.

Theorem fx_dec_enc : forall z, fx_range z -> fx_dec (fx_enc z) = z.
Proof.
  intros z H. unfold fx_dec, fx_enc.
  rewrite swrap_small; destruct sbcl_word_layout as (_ & _ & HH & _ & HF & _ & _ & _ & _ & _ & HP & HN & _);
    unfold fx_range in H; rewrite HF in *; rewrite ?HH, ?HP, ?HN in *.
  - apply Z.div_mul; lia.
  - lia.
Qed.

Theorem fx_enc_inj : forall x y, fx_range x -> fx_range y -> fx_enc x = fx_enc y -> x = y.
Proof. intros x y Hx Hy E; rewrite <- (fx_dec_enc x Hx), <- (fx_dec_enc y Hy), E; reflexivity. Qed.

(* Every even word is the encoding of exactly one fixnum. *)
Theorem fx_enc_dec : forall w, word_ok w -> fixnum_tagged w -> fx_range (fx_dec w) /\ fx_enc (fx_dec w) = w.
Proof.
  intros w Hw Ht.
  assert (Hm : w mod 2 = 0).
  { destruct sbcl_word_layout as (_ & _ & _ & _ & _ & HK & _); unfold fixnum_tagged in Ht; rewrite HK in Ht.
    change 1 with (Z.ones 1) in Ht; rewrite Z.land_ones in Ht by lia; exact Ht. }
  pose proof (swrap_range w) as R.
  assert (Hs : (swrap w) mod 2 = 0).
  { destruct sbcl_word_layout as (_ & HM & HH & _); unfold swrap; rewrite HM, HH.
    rewrite Zminus_mod, <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 9223372036854775808; reflexivity].
    rewrite Zplus_mod, Hm; reflexivity. }
  assert (He : swrap w = 2 * (swrap w / 2)) by (apply Z_div_exact_2; lia).
  destruct sbcl_word_layout as (_ & HM & HH & _ & HF & _ & _ & _ & _ & _ & HP & HN & _).
  unfold fx_dec, fx_range, fx_enc; rewrite HF, HP, HN; rewrite HH in R.
  split; [lia|].
  rewrite Z.mul_comm, <- He.
  unfold wrap, swrap; rewrite HM, HH; unfold word_ok in Hw; rewrite HM in Hw.
  destruct (Z.lt_ge_cases w 9223372036854775808).
  - rewrite (Z.mod_small (w + 9223372036854775808)) by lia. rewrite Z.mod_small; lia.
  - rewrite <- (Z.mod_unique (w + 9223372036854775808) 18446744073709551616 1
               (w + 9223372036854775808 - 18446744073709551616)) by lia.
    symmetry; apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Theorem fx_enc_signed : forall z, fx_range z -> swrap (fx_enc z) = z * 2.
Proof.
  intros z H; unfold fx_enc; destruct sbcl_word_layout as (_ & _ & HH & _ & HF & _ & _ & _ & _ & _ & HP & HN & _).
  rewrite HF; apply swrap_small; unfold fx_range in H; rewrite HH; rewrite HP, HN in H; lia.
Qed.

Theorem fx_add_wrap : forall x y, wrap (fx_enc x + fx_enc y) = fx_enc (x + y).
Proof. intros x y; unfold fx_enc, wrap; rewrite <- Zplus_mod; f_equal; ring. Qed.

(* The ADDS/BVS check of a tagged fixnum addition is a fixnum-range test. *)
Theorem fx_add_no_overflow_iff : forall x y, fx_range x -> fx_range y ->
  (- half <= swrap (fx_enc x) + swrap (fx_enc y) < half <-> fx_range (x + y)).
Proof.
  intros x y Hx Hy; rewrite (fx_enc_signed x Hx), (fx_enc_signed y Hy).
  destruct sbcl_word_layout as (_ & _ & HH & _ & _ & _ & _ & _ & _ & _ & HP & HN & _).
  unfold fx_range; rewrite HH, HP, HN; lia.
Qed.

(* (a | b) & fixnum-tag-mask = 0 iff both are fixnum-tagged. *)
Theorem tag_or_iff : forall a b,
  Z.land (Z.lor a b) img_fixnum_tag_mask = 0 <-> fixnum_tagged a /\ fixnum_tagged b.
Proof.
  intros a b; unfold fixnum_tagged; rewrite Z.land_lor_distr_l; split.
  - intro H; apply Z.lor_eq_0_iff in H; exact H.
  - intros [A B]; rewrite A, B; reflexivity.
Qed.

(* Lowtags: a word's lowtag is its residue mod 16; a lowtag-t pointer to a
   16-byte aligned object is w = A + t with A mod 16 = 0, so every slot
   w - t + 8i is 8-byte aligned. *)
Lemma lowtag_mod : forall w, lowtag w = w mod 16.
Proof. intro w; consts. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lowtag_range : forall w, 0 <= lowtag w < 16.
Proof. intro w; rewrite lowtag_mod; apply Z.mod_pos_bound; lia. Qed.

Theorem slot_aligned : forall t w i, lowtag w = t -> (w - t + 8 * i) mod 8 = 0.
Proof.
  intros t w i H. rewrite lowtag_mod in H.
  rewrite (Z.div_mod w 16) by lia. rewrite H.
  replace (16 * (w / 16) + t - t + 8 * i) with ((2 * (w / 16) + i) * 8) by ring.
  apply Z.mod_mul; lia.
Qed.

End SbclWord.
