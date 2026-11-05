(* E2E-21 host-operation contracts at the SBCL 2.6.8 arm64 representation
   level, and the CL lowering theorems with those contracts discharged.

   CLContracts.cl_host_ops names 16 SBCL operations on the CL-model values
   [sv] of CLLowering. Ten of them are inline type tests in the pinned image
   (SbclTests: EQ, TYPEP FIXNUM, INTEGERP, NUMBERP, CONSP, STRINGP, ARRAYP,
   SYMBOLP, NOT, NULL). This module
   1. relates [sv] values to SBCL words in a memory snapshot ([cv]): NIL is
      the empty list, a symbol is an interned symbol object, a string a
      simple-character-string or simple-base-string, a number spelled as a
      canonical integer a fixnum or a (normalised) bignum, any other number
      spelling a double-float object or a single-float immediate (the CL
      reader's default float format is single-float), a host object a
      simple-vector, function, instance or character, a cons a cons cell;
   2. proves, for every well-formed snapshot and every representation of the
      arguments, that the captured code returns the word that represents
      exactly the contract's answer ([*_machine]); for EQ it returns the
      identity of the two words, which is sound, and complete when either
      side is a symbol or NIL ([eq_machine]);
   3. defines the host table [sbcl_host] whose ten E2E-21 entries are those
      answers and whose other entries are a table [h24] satisfying only the
      six E2E-24 contracts ([cl_e2e24_ops]: STRING=, EQUAL twice, EQL vs =,
      = symmetric, = reflexive, all full calls in the pinned image,
      SbclTests.full_calls), proves [cl_host_ops] for it, and restates
      CLContracts.discharged_optimise_sound / discharged_emit_if_refines with
      only [cl_e2e24_ops] and [cl_kernel_ops] (and the theorems' own qsafe)
      left as premises.

   EQ is not a function of [sv] values: SBCL answers T for one cons compared
   with itself and NIL for two equal fresh conses. The composed theorems hold
   for every EQ answer function [e] that is admissible ([eq_admissible]:
   sound, and complete on symbols and NIL); [eq_machine] shows every machine
   answer on represented values has exactly those two properties, and
   [eq_fresh] (true only on identical symbols and NIL) is one admissible
   choice, used in the corollaries without the [e] premise. *)
From Coq Require Import String List Bool Ascii ZArith Lia NArith.
From Buri Require Import CLLowering.
From Buri Require Native KLSyntax CLWrappers CLContracts CLLoweringCapture SbclLayout SbclWord SbclA64
  SbclTests SbclValues.
Import ListNotations.
Open Scope string_scope.
Module SbclHostOps.
Module W := CLWrappers.CLWrappers.
Module C := CLContracts.CLContracts.
Module L := SbclLayout.SbclLayout.
Module SW := SbclWord.SbclWord.
Module A := SbclA64.SbclA64.
Module T := SbclTests.SbclTests.
Module V := SbclValues.SbclValues.

(* ---------------------------------------------------------------- number spellings *)

(* A canonical integer spelling (the Shen-CL printer's). *)
Definition int_spelling (s : string) : option Z :=
  match W.zinv s with Some z => if String.eqb (Native.Native.spelling z) s then Some z else None | None => None end.
Lemma int_spelling_zs : forall z, int_spelling (Native.Native.spelling z) = Some z.
Proof. intro z. unfold int_spelling. rewrite W.zinv_zs, String.eqb_refl. reflexivity. Qed.
Lemma int_spelling_some : forall s z, int_spelling s = Some z -> s = Native.Native.spelling z.
Proof.
  intros s z. unfold int_spelling. destruct (W.zinv s) as [y|]; [|discriminate].
  destruct (String.eqb (Native.Native.spelling y) s) eqn:E; [|discriminate]. intro X; injection X as <-.
  apply String.eqb_eq in E. symmetry; exact E.
Qed.

Lemma of_string_inj : forall s t, KLSyntax.KLSyntax.of_string s = KLSyntax.KLSyntax.of_string t -> s = t.
Proof.
  unfold KLSyntax.KLSyntax.of_string.
  induction s as [|a s IH]; intros [|b t] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hst. apply Nnat.Nat2N.inj in Hab.
  rewrite <- (ascii_nat_embedding a), <- (ascii_nat_embedding b), Hab. f_equal. apply IH; exact Hst.
Qed.

(* ---------------------------------------------------------------- snapshot and relation *)

Inductive okind := OVec | OFun | OInst | OChar.
Definition okind_vec (k : okind) : bool := match k with OVec => true | _ => false end.
Definition obj_at (m : V.mem) (k : okind) (w : Z) : Prop :=
  match k with
  | OVec => V.vector_hdr m w
  | OFun => V.fun_at m w
  | OInst => V.instance_at m w
  | OChar => exists c, (0 <= c < L.img_char_code_limit)%Z /\ w = (c * 256 + L.img_character_widetag)%Z end.

Record snapshot := {
  s_mem : V.mem;
  s_sym : string -> option Z;           (* interned symbol of each name *)
  s_obj : nat -> option Z;              (* word of each host object *)
  s_kind : nat -> okind;
  s_flo : string -> option (bool * N) }. (* float spellings: (double?, bits) *)

(* Well-formed snapshot: interning, object identity and float spellings are
   injective; T is the symbol at NIL + 56 (the image); NIL's layout is
   genesis.lisp's. *)
Definition snap_wf (S : snapshot) : Prop :=
  (forall s1 s2 w, s_sym S s1 = Some w -> s_sym S s2 = Some w -> s1 = s2) /\
  s_sym S "T" = Some T.tv /\ V.symbol_at (s_mem S) T.tv /\
  (forall n1 n2 w, s_obj S n1 = Some w -> s_obj S n2 = Some w -> n1 = n2) /\
  (forall s1 s2 x, s_flo S s1 = Some x -> s_flo S s2 = Some x -> s1 = s2) /\
  V.nil_layout (s_mem S).

Section Rel.
Variable S : snapshot.
Let m := s_mem S.

Inductive cv : sv -> Z -> Prop :=
 | CNil : cv VNil T.nilv
 | CSym : forall s w, s_sym S s = Some w -> V.symbol_at m w -> cv (VSym s) w
 | CStr : forall s w, V.string_at m w (KLSyntax.KLSyntax.of_string s) -> cv (VStr s) w
 | CFix : forall s z, int_spelling s = Some z -> SW.fx_range z -> cv (VNum s) (SW.fx_enc z)
 | CBig : forall s z w, int_spelling s = Some z -> ~ SW.fx_range z -> V.bignum_at m w z -> cv (VNum s) w
 | CDbl : forall s b w, int_spelling s = None -> s_flo S s = Some (true, b) -> V.double_at m w b -> cv (VNum s) w
 | CSgl : forall s b, int_spelling s = None -> s_flo S s = Some (false, b) -> (b < 2 ^ 32)%N ->
     cv (VNum s) (Z.of_N b * 2 ^ 32 + L.img_single_float_widetag)%Z
 | CObj : forall n w, s_obj S n = Some w -> obj_at m (s_kind S n) w -> cv (VObj n) w
 | CCons : forall a b w, V.cons_ok w -> cv a (V.car_w m w) -> cv b (V.cdr_w m w) -> cv (VCons a b) w.

(* The contract-level answers on [sv]. *)
Definition sv_integerp (a : sv) : bool :=
  match a with VNum s => match int_spelling s with Some _ => true | None => false end | _ => false end.
Definition sv_fixnump (a : sv) : bool :=
  match a with VNum s => match int_spelling s with Some z => SW.fx_rangeb z | None => false end | _ => false end.
Definition sv_arrayp (a : sv) : bool :=
  match a with VStr _ => true | VObj n => okind_vec (s_kind S n) | _ => false end.

(* ---------------------------------------------------------------- word facts *)

Lemma pow32 : (2 ^ 32 = 16 * 268435456)%Z.
Proof. reflexivity. Qed.

Lemma single_facts : forall b, (b < 2 ^ 32)%N ->
  let w := (Z.of_N b * 2 ^ 32 + 25)%Z in
  Z.testbit w 0 = true /\ (A.trunc 32 w =? 25)%Z = true /\ (Z.land w 15 =? 15)%Z = false /\
  (Z.land w 15 =? 7)%Z = false /\ (w =? T.nilv)%Z = false /\ (0 <= w < 2 ^ 64)%Z.
Proof.
  intros b Hb w.
  assert (Hb' : (0 <= Z.of_N b < 2 ^ 32)%Z).
  { split; [lia|]. apply N2Z.inj_lt in Hb. rewrite N2Z.inj_pow in Hb. exact Hb. }
  assert (L : (w mod 16 = 9)%Z).
  { unfold w. rewrite pow32. replace (Z.of_N b * (16 * 268435456) + 25)%Z with (25 + (Z.of_N b * 268435456) * 16)%Z by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (L15 : Z.land w 15 = 9%Z) by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; exact L).
  assert (Odd : Z.testbit w 0 = true).
  { rewrite Z.testbit_true by lia. change (2 ^ 0)%Z with 1%Z. rewrite Z.div_1_r.
    rewrite (Z.div_mod w 16) by lia. rewrite L.
    replace (16 * (w / 16) + 9)%Z with (1 + (8 * (w / 16) + 4) * 2)%Z by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  split; [exact Odd|]. split.
  - apply Z.eqb_eq. unfold A.trunc, w. replace (Z.of_N b * 2 ^ 32 + 25)%Z with (25 + Z.of_N b * 2 ^ 32)%Z by ring. rewrite Z.mod_add by lia. reflexivity.
  - rewrite L15. split; [reflexivity|]. split; [reflexivity|]. split.
    + apply Z.eqb_neq. intro E. rewrite E in L. vm_compute in L. discriminate.
    + unfold w. split; [lia|]. nia.
Qed.

Lemma char_facts : forall c, (0 <= c < L.img_char_code_limit)%Z ->
  let w := (c * 256 + L.img_character_widetag)%Z in
  Z.testbit w 0 = true /\ (A.trunc 32 w =? 25)%Z = false /\ (Z.land w 15 =? 15)%Z = false /\
  (Z.land w 15 =? 7)%Z = false /\ (w =? T.nilv)%Z = false /\ (0 <= w < 2 ^ 64)%Z.
Proof.
  intros c Hc w. change L.img_char_code_limit with 1114112%Z in Hc. change L.img_character_widetag with 81%Z in w.
  assert (L : (w mod 16 = 1)%Z).
  { unfold w. replace (c * 256 + 81)%Z with (1 + (c * 16 + 5) * 16)%Z by ring. rewrite Z.mod_add by lia. reflexivity. }
  assert (L15 : Z.land w 15 = 1%Z) by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; exact L).
  assert (Odd : Z.testbit w 0 = true).
  { rewrite Z.testbit_true by lia. change (2 ^ 0)%Z with 1%Z. rewrite Z.div_1_r.
    unfold w. replace (c * 256 + 81)%Z with (1 + (c * 128 + 40) * 2)%Z by ring. rewrite Z.mod_add by lia. reflexivity. }
  split; [exact Odd|]. split.
  - apply Z.eqb_neq. intro E. unfold A.trunc in E.
    assert (M : ((w mod 2 ^ 32) mod 256 = 81)%Z).
    { rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 16777216%Z; reflexivity].
      unfold w. replace (c * 256 + 81)%Z with (81 + c * 256)%Z by ring. rewrite Z.mod_add by lia. reflexivity. }
    rewrite E in M. discriminate.
  - rewrite L15. split; [reflexivity|]. split; [reflexivity|]. split.
    + apply Z.eqb_neq. intro E. rewrite E in L. vm_compute in L. discriminate.
    + unfold w. lia.
Qed.

Ltac imm_tests F :=
  destruct F as (Odd & Sg & L1 & L2 & N & _);
  unfold T.t_consp, T.t_null, T.t_fixnump, T.t_integerp, T.t_numberp, T.t_stringp, T.t_arrayp, T.t_symbolp;
  rewrite Odd, Sg, L1, L2, N; cbn.

Ltac lay := pose proof V.sbcl_object_layout as (HL3 & HL7 & HL11 & HL15 & HWB & HWD & HWS & HWV & HWBS & HWCS &
  HWI & HWSF & HWC & HWFI & HWCh & HWSg & _).

(* The word-level tests on every represented value are the contract's answers. *)
Theorem cv_tests : forall a w, cv a w ->
  T.t_consp w = is_cons a /\ T.t_null w = is_nil a /\ T.t_fixnump w = sv_fixnump a /\
  T.t_integerp m w = sv_integerp a /\ T.t_numberp m w = is_num a /\ T.t_stringp m w = is_str a /\
  T.t_arrayp m w = sv_arrayp a /\ T.t_symbolp m w = symbolic a.
Proof.
  intros a w H; lay; destruct H; cbn [is_cons is_nil sv_fixnump sv_integerp is_num is_str sv_arrayp symbolic].
  - destruct (V.nil_tests m) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). repeat split; assumption.
  - unfold V.symbol_at in H0. rewrite HWS in H0. destruct (V.other_tests_lemma m _ _ H0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - destruct (V.string_other m _ _ H) as (wt & O & [-> | ->]);
    destruct (V.other_tests_lemma m _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8);
    rewrite A1, A2, A3, A4, A5, A6, A7, A8; repeat split; reflexivity.
  - rewrite H. destruct (V.fx_tests m z) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. apply SW.fx_rangeb_spec in H0. rewrite H0. repeat split; reflexivity.
  - rewrite H. destruct H1 as (O & _). rewrite HWB in O. destruct (V.other_tests_lemma m _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. destruct (SW.fx_rangeb z) eqn:Q; [apply SW.fx_rangeb_spec in Q; contradiction|].
    repeat split; reflexivity.
  - rewrite H. destruct H1 as (O & _). rewrite HWD in O. destruct (V.other_tests_lemma m _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - rewrite H. rewrite HWSg. pose proof (single_facts b H1) as F. imm_tests F. repeat split; reflexivity.
  - destruct (s_kind S n) eqn:K; cbn in H0 |- *.
    + unfold V.vector_hdr in H0. rewrite HWV in H0. destruct (V.other_tests_lemma m _ _ H0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
    + destruct H0 as (P & _). rewrite HL11 in P. destruct (V.ptr_tests m 11 _ P ltac:(cbn; tauto)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
    + destruct H0 as (P & _). rewrite HL3 in P. destruct (V.ptr_tests m 3 _ P ltac:(cbn; tauto)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
    + destruct H0 as (c & Hc & ->). pose proof (char_facts c Hc) as F. imm_tests F. repeat split; reflexivity.
  - destruct (V.cons_tests m _ H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
Qed.

Lemma cv_word : forall a w, cv a w -> (0 <= w < 2 ^ 64)%Z.
Proof.
  intros a w H; destruct H.
  - vm_compute. split; congruence.
  - destruct H0 as (P & _). exact (V.ptr_word _ _ P).
  - destruct (V.string_other m _ _ H) as (wt & (P & _) & _). exact (V.ptr_word _ _ P).
  - pose proof (SW.fx_enc_word z) as X. unfold SW.word_ok, SW.modulus in X. exact X.
  - destruct H1 as ((P & _) & _). exact (V.ptr_word _ _ P).
  - destruct H1 as ((P & _) & _). exact (V.ptr_word _ _ P).
  - change L.img_single_float_widetag with 25%Z. apply (single_facts b H1).
  - destruct (s_kind S n); cbn in H0.
    + destruct H0 as (P & _). exact (V.ptr_word _ _ P).
    + destruct H0 as (P & _). exact (V.ptr_word _ _ P).
    + destruct H0 as (P & _). exact (V.ptr_word _ _ P).
    + destruct H0 as (c & Hc & ->). apply (char_facts c Hc).
  - destruct H as (P & _). exact (V.ptr_word _ _ P).
Qed.

Lemma lowtag15_of : forall w, (Z.land w 15 =? 15)%Z = true -> T.t_arrayp m w = (129 <=? T.hdr m w)%Z.
Proof. intros w E. unfold T.t_arrayp. rewrite E. reflexivity. Qed.

Lemma fx_rangeb_false : forall z, ~ SW.fx_range z -> SW.fx_rangeb z = false.
Proof. intros z H. destruct (SW.fx_rangeb z) eqn:Q; [apply SW.fx_rangeb_spec in Q; contradiction | reflexivity]. Qed.
Ltac spell := repeat match goal with
  | E : int_spelling ?x = _, X : context [int_spelling ?x] |- _ => rewrite E in X end.
Ltac fr := repeat match goal with
  | E : SW.fx_range ?z, X : context [SW.fx_rangeb ?z] |- _ => rewrite (proj2 (SW.fx_rangeb_spec z) E) in X
  | E : ~ SW.fx_range ?z, X : context [SW.fx_rangeb ?z] |- _ => rewrite (fx_rangeb_false z E) in X end.
Ltac spell2 := repeat match goal with E : int_spelling _ = Some _ |- _ => apply int_spelling_some in E; subst end.
Ltac dbl_sgl := exfalso; match goal with D : V.double_at _ _ _, Sg : (?b < 2 ^ 32)%N |- _ =>
  let P := fresh in let Lw := fresh in let L1 := fresh in
  destruct D as ((P & _) & _); destruct P as (_ & Lw & _); rewrite V.lowtag_land in Lw;
  pose proof (single_facts b Sg) as (_ & _ & L1 & _); change L.img_single_float_widetag with 25%Z in *;
  rewrite Lw in L1; discriminate end.

Ltac tests_of H := let A1 := fresh "A" in let A2 := fresh "A" in let A3 := fresh "A" in let A4 := fresh "A" in
  let A5 := fresh "A" in let A6 := fresh "A" in let A7 := fresh "A" in let A8 := fresh "A" in
  pose proof (cv_tests _ _ H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
Ltac clash := match goal with A : ?t = ?x, B : ?t = ?y |- _ =>
  let E := fresh in assert (E : x = y) by (rewrite <- A; exact B); discriminate E end.
Ltac cvsimp := repeat match goal with X : _ = ?r |- _ =>
  lazymatch r with
  | is_cons _ => idtac | is_nil _ => idtac | sv_fixnump _ => idtac | sv_integerp _ => idtac
  | is_num _ => idtac | is_str _ => idtac | sv_arrayp _ => idtac | symbolic _ => idtac end;
  progress (cbn [is_cons is_nil sv_fixnump sv_integerp is_num is_str sv_arrayp symbolic] in X) end.

(* With injective interning, object identity and float spellings, a word
   represents at most one [sv] value: EQ on words is sound. *)
Theorem cv_functional : snap_wf S -> forall a w, cv a w -> forall b, cv b w -> a = b.
Proof.
  intros (SI & _ & _ & OI & FI & _) a w H1. induction H1 as [ | | | | | | | | a b w Hc H1a IHa H1b IHb];
    intros c H2; pose proof (cv_tests _ _ H2) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  - destruct c; cbn in B2; try discriminate; reflexivity.
  - tests_of (CSym s w H H0). inversion H2; subst; cvsimp; try solve [clash | discriminate]. f_equal. eapply SI; eassumption.
  - tests_of (CStr s w H). inversion H2; subst; cvsimp; try solve [clash | discriminate]. f_equal. apply of_string_inj.
    eapply V.string_at_functional; eassumption.
  - tests_of (CFix s z H H0). inversion H2; subst; cvsimp; spell; fr; try solve [clash | discriminate].
    match goal with E : SW.fx_enc _ = SW.fx_enc _ |- _ => apply SW.fx_enc_inj in E; [subst|assumption|assumption] end.
    spell2. reflexivity.
  - tests_of (CBig s z w H H0 H1). inversion H2; subst; cvsimp; spell; fr; try solve [clash | discriminate].
    match goal with B1 : V.bignum_at _ _ _, B2 : V.bignum_at _ _ _ |- _ =>
      destruct B1 as (_ & _ & E1), B2 as (_ & _ & E2) end. subst. spell2. reflexivity.
  - tests_of (CDbl s b w H H0 H1). inversion H2; subst; cvsimp; spell; fr; try solve [clash | discriminate | dbl_sgl].
    match goal with D1 : V.double_at _ _ ?b1, D2 : V.double_at _ _ ?b2 |- _ =>
      destruct D1 as (_ & E1), D2 as (_ & E2) end. rewrite E1 in E2. apply N2Z.inj in E2. subst.
    f_equal. eapply FI; eassumption.
  - tests_of (CSgl s b H H0 H1). inversion H2; subst; cvsimp; spell; fr; try solve [clash | discriminate | dbl_sgl].
    try (match goal with E : (Z.of_N ?b1 * _ + _ = Z.of_N ?b2 * _ + _)%Z |- _ =>
      assert (b1 = b2) by (apply N2Z.inj; cbn in E; lia) end; subst). f_equal. eapply FI; eassumption.
  - tests_of (CObj n w H H0). inversion H2; subst; cvsimp; try solve [clash | discriminate]. f_equal. eapply OI; eassumption.
  - tests_of (CCons a b w Hc H1a H1b). inversion H2; subst; cvsimp; try solve [clash | discriminate].
    f_equal; [apply IHa | apply IHb]; assumption.
Qed.

(* Symbols and NIL have exactly one word each. *)
Lemma cv_symbolic_unique : forall a w1 w2, symbolic a = true -> cv a w1 -> cv a w2 -> w1 = w2.
Proof.
  intros a w1 w2 Sy H1 H2. destruct a; cbn in Sy; try discriminate.
  - inversion H1; inversion H2; subst. congruence.
  - inversion H1; inversion H2; subst. reflexivity.
Qed.

Lemma cv_bool : forall b, snap_wf S -> cv (W.hb b) (if b then T.tv else T.nilv).
Proof. intros [|] (_ & HT & ST & _); cbn; [apply CSym; assumption | apply CNil]. Qed.

End Rel.

(* ---------------------------------------------------------------- the captured code decides the contracts *)

(* The window ends with R0 holding a word that represents v. *)
Definition answers (S : snapshot) (ws : list Z) (s : A.state) (v : sv) : Prop :=
  exists s', A.run_words (Datatypes.S (length ws)) (s_mem S) ws s = Some s' /\ cv S v (A.R s' 10).

Definition arg_regs (s : A.state) (w : Z) : Prop :=
  A.regs_ok s /\ A.R s 11 = w /\ A.R s 26 = T.nilv.

Lemma yields_answers : forall S ws s b, snap_wf S -> T.yields (s_mem S) ws s b -> answers S ws s (W.hb b).
Proof. intros S ws s b Wf (s' & E & R0). exists s'. split; [exact E|]. rewrite R0. apply cv_bool; exact Wf. Qed.

(* E2E-21 at the representation level: for every well-formed snapshot,
   every value a and every word w representing it, the captured SBCL code
   for each one-argument operation returns the representation of the
   contract's answer. *)
Theorem e2e21_machine : forall S a w s, snap_wf S -> cv S a w -> arg_regs s w ->
  answers S T.w_consp s (W.hb (is_cons a)) /\
  answers S T.w_null s (W.hb (is_nil a)) /\
  answers S T.w_not s (W.hb (is_nil a)) /\
  answers S T.w_symbolp s (W.hb (symbolic a)) /\
  answers S T.w_stringp s (W.hb (is_str a)) /\
  answers S T.w_numberp s (W.hb (is_num a)) /\
  answers S T.w_integerp s (W.hb (sv_integerp a)) /\
  answers S T.w_typep_fixnum s (W.hb (sv_fixnump a)) /\
  answers S T.w_arrayp s (W.hb (sv_arrayp S a)) /\
  (sv_integerp a = true -> is_num a = true) /\
  (sv_fixnump a = true -> is_num a = true /\ sv_integerp a = true) /\
  (is_str a = true -> sv_arrayp S a = true) /\
  (sv_arrayp S a = true -> (is_str a || C.is_obj a)%bool = true).
Proof.
  intros S a w s Wf H (Ok & H11 & H26).
  destruct (cv_tests S a w H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  repeat match goal with |- _ /\ _ => split end; try (apply yields_answers; [exact Wf|]).
  - rewrite <- A1. apply T.consp_window; assumption.
  - rewrite <- A2. apply T.null_window; assumption.
  - rewrite <- A2. apply T.not_window; assumption.
  - rewrite <- A8. apply T.symbolp_window; assumption.
  - rewrite <- A6. apply T.stringp_window; assumption.
  - rewrite <- A5. apply T.numberp_window; assumption.
  - rewrite <- A4. apply T.integerp_window; assumption.
  - rewrite <- A3. apply T.typep_fixnum_window; assumption.
  - rewrite <- A7. apply T.arrayp_window; assumption.
  - intro X; destruct a; cbn in *; try discriminate; reflexivity.
  - intro X; unfold sv_fixnump, sv_integerp in *; destruct a; try discriminate.
    destruct (int_spelling s0); [split; reflexivity|discriminate].
  - intro X; destruct a; cbn in *; try discriminate; reflexivity.
  - intro X; destruct a; cbn in *; try discriminate; reflexivity.
Qed.

(* EQ: the captured code compares the two words. Its answer is sound, and
   complete when either side is a symbol or NIL. *)
Theorem eq_machine : forall S a b x y s, snap_wf S -> cv S a x -> cv S b y ->
  A.regs_ok s -> A.R s 12 = x -> A.R s 11 = y -> A.R s 26 = T.nilv ->
  exists r, answers S T.w_eq s (W.hb r) /\ (r = true -> a = b) /\
            ((symbolic a || symbolic b)%bool = true -> a = b -> r = true).
Proof.
  intros S a b x y s Wf Ha Hb Ok H12 H11 H26. exists (T.t_eq x y). split.
  - apply yields_answers; [exact Wf|]. apply T.eq_window; assumption.
  - unfold T.t_eq. split.
    + intro E. apply Z.eqb_eq in E. rewrite <- E in Hb. apply (cv_functional S Wf a x Ha b Hb).
    + intros Sy ->. apply Z.eqb_eq. apply orb_true_iff in Sy. destruct Sy as [Sy|Sy];
        apply (cv_symbolic_unique S b x y Sy Ha Hb).
Qed.

(* ---------------------------------------------------------------- the composed host *)

(* The six E2E-24 contracts, each a full call in the pinned image. *)
Record cl_e2e24_ops (h : string -> list sv -> W.cres) : Prop := {
 e24_string_eq : forall x y, h "STRING=" [VStr x; VStr y] = W.CRet (W.hb (String.eqb x y));
 e24_equal_string : forall x a, h "EQUAL" [VStr x; a] = W.CRet (W.hb (sv_eqb (VStr x) a)) /\
   h "EQUAL" [a; VStr x] = W.CRet (W.hb (sv_eqb a (VStr x)));
 e24_equal_object : forall n b, C.is_obj b = false -> h "EQUAL" [VObj n; b] = W.CRet VNil;
 e24_eql_integer : forall a b, sv_integerp a = true -> sv_integerp b = true -> h "EQL" [a; b] = h "=" [a; b];
 e24_num_eq_sym : forall a b, is_num a = true -> is_num b = true -> h "=" [a; b] = h "=" [b; a];
 e24_num_eq_refl : forall n, h "=" [VNum n; VNum n] = W.CRet W.T }.

Definition sv_arrayp_k (K : nat -> okind) (a : sv) : bool :=
  match a with VStr _ => true | VObj n => okind_vec (K n) | _ => false end.
Lemma sv_arrayp_k_eq : forall S a, sv_arrayp S a = sv_arrayp_k (s_kind S) a.
Proof. reflexivity. Qed.

Definition eq_admissible (e : sv -> sv -> bool) : Prop :=
  forall a b, (e a b = true -> a = b) /\ ((symbolic a || symbolic b)%bool = true -> a = b -> e a b = true).
Definition eq_fresh (a b : sv) : bool := ((symbolic a || symbolic b) && sv_eqb a b)%bool.
Lemma eq_fresh_admissible : eq_admissible eq_fresh.
Proof.
  intros a b. unfold eq_fresh. split.
  - intro E. apply andb_true_iff in E as [_ E]. apply sv_eqb_eq. exact E.
  - intros Sy ->. rewrite Sy. cbn. apply sv_eqb_eq. reflexivity.
Qed.

(* E2E-21 entries are the captured code's answers; every other head is h24. *)
Definition sbcl_host (K : nat -> okind) (e : sv -> sv -> bool) (h24 : string -> list sv -> W.cres)
    (f : string) (vs : list sv) : W.cres :=
  match f, vs with
  | "EQ", [a; b] => W.CRet (W.hb (e a b))
  | "TYPEP", [a; VSym "FIXNUM"] => W.CRet (W.hb (sv_fixnump a))
  | "INTEGERP", [a] => W.CRet (W.hb (sv_integerp a))
  | "NUMBERP", [a] => W.CRet (W.hb (is_num a))
  | "CONSP", [a] => W.CRet (W.hb (is_cons a))
  | "STRINGP", [a] => W.CRet (W.hb (is_str a))
  | "ARRAYP", [a] => W.CRet (W.hb (sv_arrayp_k K a))
  | "SYMBOLP", [a] => W.CRet (W.hb (symbolic a))
  | "NOT", [a] => W.CRet (W.hb (is_nil a))
  | "NULL", [a] => W.CRet (W.hb (is_nil a))
  | _, _ => h24 f vs end.

Lemma hb_T : forall b, W.CRet (W.hb b) = W.CRet W.T -> b = true.
Proof. intros [|] E; [reflexivity|discriminate]. Qed.

Theorem sbcl_host_ops : forall K e h24, eq_admissible e -> cl_e2e24_ops h24 -> C.cl_host_ops (sbcl_host K e h24).
Proof.
  intros K e h24 Ea E. constructor; cbn.
  - intros a b. exists (e a b). split; [reflexivity|]. apply Ea.
  - intros a. exists (sv_fixnump a). split; [reflexivity|]. intro F. unfold sv_fixnump, sv_integerp in *.
    destruct a; try discriminate. destruct (int_spelling s); [|discriminate]. split; reflexivity.
  - intros a. exists (sv_integerp a). split; [reflexivity|]. destruct a; cbn; try discriminate; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a. exists (sv_arrayp_k K a). split; [reflexivity|]. split.
    + destruct a; cbn; try discriminate; reflexivity.
    + destruct a; cbn; try discriminate; reflexivity.
  - reflexivity.
  - apply (e24_string_eq h24 E).
  - reflexivity.
  - reflexivity.
  - apply (e24_equal_string h24 E).
  - apply (e24_equal_object h24 E).
  - intros a b Ia Ib. apply hb_T in Ia, Ib. apply (e24_eql_integer h24 E); assumption.
  - apply (e24_num_eq_sym h24 E).
  - apply (e24_num_eq_refl h24 E).
Qed.

(* The host's E2E-21 entries are what the captured code computes, on every
   representation of the arguments in every well-formed snapshot with the
   same host-object kinds. *)
Theorem sbcl_host_is_machine : forall K e h24 S a w s, snap_wf S -> s_kind S = K -> cv S a w -> arg_regs s w ->
  (exists v, sbcl_host K e h24 "CONSP" [a] = W.CRet v /\ answers S T.w_consp s v) /\
  (exists v, sbcl_host K e h24 "NULL" [a] = W.CRet v /\ answers S T.w_null s v) /\
  (exists v, sbcl_host K e h24 "NOT" [a] = W.CRet v /\ answers S T.w_not s v) /\
  (exists v, sbcl_host K e h24 "SYMBOLP" [a] = W.CRet v /\ answers S T.w_symbolp s v) /\
  (exists v, sbcl_host K e h24 "STRINGP" [a] = W.CRet v /\ answers S T.w_stringp s v) /\
  (exists v, sbcl_host K e h24 "NUMBERP" [a] = W.CRet v /\ answers S T.w_numberp s v) /\
  (exists v, sbcl_host K e h24 "INTEGERP" [a] = W.CRet v /\ answers S T.w_integerp s v) /\
  (exists v, sbcl_host K e h24 "TYPEP" [a; VSym "FIXNUM"] = W.CRet v /\ answers S T.w_typep_fixnum s v) /\
  (exists v, sbcl_host K e h24 "ARRAYP" [a] = W.CRet v /\ answers S T.w_arrayp s v).
Proof.
  intros K e h24 S a w s Wf Hk H R.
  destruct (e2e21_machine S a w s Wf H R) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & _).
  rewrite sv_arrayp_k_eq, Hk in M9.
  repeat match goal with |- _ /\ _ => split end; eexists; (split; [reflexivity|]); eassumption.
Qed.

(* ---------------------------------------------------------------- the lowering theorems *)

(* CLContracts.discharged_optimise_sound / discharged_emit_if_refines with
   the ten E2E-21 fields of cl_host_ops replaced by the captured-code
   theorems above: the remaining premises are the six E2E-24 contracts, the
   compiled kernel functions (cl_kernel_ops, E2E-16), an admissible EQ
   answer, and qsafe. *)
Theorem sbcl_optimise_sound : forall St K e h24 kern other ce n v r,
  eq_admissible e -> cl_e2e24_ops h24 -> C.cl_kernel_ops St kern ->
  run n (lowering_defs CLLoweringCapture.captured_lowering) ce OPT [v] = LOk r -> qsafe v = true ->
  W.admission = Some W.program /\ OptEquiv St (C.captured_prim St (sbcl_host K e h24) kern other) other v r.
Proof. intros. eapply C.discharged_optimise_sound; eauto. apply sbcl_host_ops; assumption. Qed.

Theorem sbcl_emit_if_refines : forall St K e h24 kern other ce n t th el sc r,
  eq_admissible e -> cl_e2e24_ops h24 -> C.cl_kernel_ops St kern ->
  run n (lowering_defs CLLoweringCapture.captured_lowering) ce EMIT_IF [t; th; el; sc] = LOk r ->
  W.admission = Some W.program /\
  ((t = VSym "true" /\ ce th sc = LOk r) \/ (t = VSym "false" /\ ce el sc = LOk r) \/
   (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\
     (qsafe c = true -> forall e' s o, ev St (C.captured_prim St (sbcl_host K e h24) kern other) other e' r s o <->
                                      shen_if St (C.captured_prim St (sbcl_host K e h24) kern other) other e' c a b s o))).
Proof. intros. eapply C.discharged_emit_if_refines; eauto. apply sbcl_host_ops; assumption. Qed.

(* The same with the admissible EQ answer fixed: only E2E-24 and the kernel
   contracts remain. *)
Corollary sbcl_optimise_sound_e24 : forall St K h24 kern other ce n v r,
  cl_e2e24_ops h24 -> C.cl_kernel_ops St kern ->
  run n (lowering_defs CLLoweringCapture.captured_lowering) ce OPT [v] = LOk r -> qsafe v = true ->
  W.admission = Some W.program /\ OptEquiv St (C.captured_prim St (sbcl_host K eq_fresh h24) kern other) other v r.
Proof. intros. eapply sbcl_optimise_sound; eauto. apply eq_fresh_admissible. Qed.

Corollary sbcl_emit_if_refines_e24 : forall St K h24 kern other ce n t th el sc r,
  cl_e2e24_ops h24 -> C.cl_kernel_ops St kern ->
  run n (lowering_defs CLLoweringCapture.captured_lowering) ce EMIT_IF [t; th; el; sc] = LOk r ->
  W.admission = Some W.program /\
  ((t = VSym "true" /\ ce th sc = LOk r) \/ (t = VSym "false" /\ ce el sc = LOk r) \/
   (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\
     (qsafe c = true -> forall e' s o, ev St (C.captured_prim St (sbcl_host K eq_fresh h24) kern other) other e' r s o <->
                                      shen_if St (C.captured_prim St (sbcl_host K eq_fresh h24) kern other) other e' c a b s o))).
Proof. intros. eapply sbcl_emit_if_refines; eauto. apply eq_fresh_admissible. Qed.

(* ---------------------------------------------------------------- anti-vacuity *)

(* The E2E-24 record is satisfiable (CLContracts.model_host, not a model of SBCL). *)
Theorem e24_satisfiable : cl_e2e24_ops C.model_host.
Proof.
  constructor; cbn.
  - reflexivity.
  - intros x a. split; [reflexivity|]. destruct a; reflexivity.
  - intros n b E. reflexivity.
  - reflexivity.
  - intros a b _ _. rewrite sv_eqb_sym. reflexivity.
  - intros n. rewrite String.eqb_refl. reflexivity.
Qed.

(* A well-formed snapshot: NIL laid out as in genesis.lisp, T a symbol,
   nothing else interned. *)
Definition le_bytes (v a0 a : Z) : Z := Z.shiftr v (8 * (a - a0)) mod 256.
Definition ex_mem (a : Z) : Z :=
  if ((T.nilv - 7 <=? a) && (a <? T.nilv + 9))%Z%bool then
    (if (a <? T.nilv + 1)%Z then le_bytes T.nilv (T.nilv - 7) a else le_bytes T.nilv (T.nilv + 1) a)
  else if (a =? T.nilv - 15)%Z then 45%Z
  else if (a =? T.tv - 15)%Z then 45%Z else 0%Z.
Definition ex_snap : snapshot := {|
  s_mem := ex_mem; s_sym := fun s => if String.eqb s "T" then Some T.tv else None;
  s_obj := fun _ => None; s_kind := fun _ => OVec; s_flo := fun _ => None |}.

Theorem ex_snap_wf : snap_wf ex_snap.
Proof.
  unfold snap_wf. cbn. split.
  { intros s1 s2 w E1 E2. destruct (String.eqb s1 "T") eqn:A, (String.eqb s2 "T") eqn:B; try discriminate.
    apply String.eqb_eq in A, B. congruence. }
  split; [reflexivity|]. split.
  { unfold V.symbol_at, V.other_at, V.ptr_ok, V.widetag_at, SW.word_ok, SW.lowtag. vm_compute. repeat split; congruence. }
  split; [intros n1 n2 w E; discriminate|]. split; [intros s1 s2 x E; discriminate|].
  unfold V.nil_layout, V.car_w, V.cdr_w, V.slot, V.load64, V.widetag_at. vm_compute. repeat split; reflexivity.
Qed.

Theorem ex_snap_values : cv ex_snap VNil T.nilv /\ cv ex_snap (VSym "T") T.tv /\
  cv ex_snap (W.zs 5) (SW.fx_enc 5).
Proof.
  split; [apply CNil|]. split.
  - apply CSym; [reflexivity|]. unfold V.symbol_at, V.other_at, V.ptr_ok, V.widetag_at, SW.word_ok, SW.lowtag.
    vm_compute. repeat split; congruence.
  - apply CFix; [apply int_spelling_zs|]. unfold SW.fx_range. vm_compute. split; congruence.
Qed.

End SbclHostOps.
