(** * Bit-level equalities of shift-and-mask words, by testing each of the 64 bits.

    [bits] proves [Z_to_bv 64 L = Z_to_bv 64 R] when L and R are built from bytes (each below 256),
    literals, [Z.land], [Z.lor], [Z.lxor], [Z.shiftl], [Z.shiftr], [bv_wrap] and [bv_swrap], as the
    [v_*] value forms of Theorem's library leave them.  It unfolds the forms, then for each bit index
    below 64 rewrites [Z.testbit] down to bits of the input bytes, and compares.  Proof-side only. *)

From Stdlib Require Import NArith ZArith List Lia Bool Btauto.
Import ListNotations.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Common Require Import PropExec StepTac.
Open Scope Z_scope.

Lemma tb_wrap : forall n z i, 0 <= i -> Z.testbit (bv_wrap n z) i = (i <? Z.of_N n) && Z.testbit z i.
Proof.
  intros n z i Hi. rewrite bv_wrap_spec by exact Hi.
  destruct (Z.ltb_spec i (Z.of_N n)); [rewrite bool_decide_true by lia | rewrite bool_decide_false by lia];
    destruct (Z.testbit z i); reflexivity.
Qed.

Lemma tb_swrap : forall n z i, 0 <= i ->
  Z.testbit (bv_swrap n z) i = if i <? Z.of_N n - 1 then Z.testbit z i else Z.testbit z (Z.of_N n - 1).
Proof.
  intros n z i Hi. rewrite bv_swrap_spec by exact Hi.
  destruct (Z.ltb_spec i (Z.of_N n - 1)); [rewrite bool_decide_true by lia | rewrite bool_decide_false by lia];
    reflexivity.
Qed.

Lemma tb_small : forall b k i, 0 <= b < 2 ^ k -> 0 <= k -> k <= i -> Z.testbit b i = false.
Proof.
  intros b k i Hb Hk Hi. destruct (Z.eq_dec b 0) as [->|Hn]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. assert (Z.log2 b < k) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Ltac v_unfold :=
  unfold v_addi, v_add, v_sub, v_andi, v_ori, v_xori, v_and, v_or, v_xor, v_slli, v_srli, v_srai,
    v_sll, v_srl, v_lui, v_addiw, v_slliw, v_srliw, v_sraiw in *;
  rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed.

(** ** Reflection: expressions, their bits as formulas over input bits, and a checker. *)

Inductive bx := BLit (z : Z) | BVar (k : nat) | BAnd (a b : bx) | BOr (a b : bx) | BXor (a b : bx)
              | BShl (a : bx) (n : Z) | BShr (a : bx) (n : Z) | BWrap (n : N) (a : bx) | BSwrap (n : N) (a : bx)
              | BAdd (a b : bx).

Section Den.
Variable env : list Z.     (* input values *)
Variable ws : list Z.      (* their widths: 0 <= value < 2^width *)

Fixpoint bden (e : bx) : Z :=
  match e with
  | BLit z => z | BVar k => nth k env 0
  | BAnd a b => Z.land (bden a) (bden b) | BOr a b => Z.lor (bden a) (bden b) | BXor a b => Z.lxor (bden a) (bden b)
  | BShl a n => Z.shiftl (bden a) n | BShr a n => Z.shiftr (bden a) n
  | BWrap n a => bv_wrap n (bden a) | BSwrap n a => bv_swrap n (bden a)
  | BAdd a b => bden a + bden b
  end.

Inductive bf := FT | FF | FA (k : nat) (j : Z) | FAnd (a b : bf) | FOr (a b : bf) | FXor (a b : bf).

Fixpoint fden (f : bf) : bool :=
  match f with
  | FT => true | FF => false | FA k j => Z.testbit (nth k env 0) j
  | FAnd a b => fden a && fden b | FOr a b => fden a || fden b | FXor a b => xorb (fden a) (fden b)
  end.

Definition fand (a b : bf) : bf :=
  match a, b with FF, _ | _, FF => FF | FT, x | x, FT => x | _, _ => FAnd a b end.
Definition f_or (a b : bf) : bf :=
  match a, b with FT, _ | _, FT => FT | FF, x | x, FF => x | _, _ => FOr a b end.
Definition fxor (a b : bf) : bf :=
  match a, b with FF, x | x, FF => x | _, _ => FXor a b end.

Lemma fand_ok : forall a b, fden (fand a b) = fden a && fden b.
Proof. destruct a, b; cbn; rewrite ?andb_true_r, ?andb_false_r; reflexivity. Qed.
Lemma f_or_ok : forall a b, fden (f_or a b) = fden a || fden b.
Proof. destruct a, b; cbn; rewrite ?orb_true_r, ?orb_false_r; reflexivity. Qed.
Lemma fxor_ok : forall a b, fden (fxor a b) = xorb (fden a) (fden b).
Proof. destruct a, b; cbn; rewrite ?xorb_false_r; reflexivity. Qed.

Definition omap2 {A} (f : A -> A -> A) (x y : option A) : option A :=
  match x, y with Some a, Some b => Some (f a b) | _, _ => None end.

(** A width: [bw e = Some w] means 0 <= bden e < 2^w. *)
Fixpoint bw (e : bx) : option Z :=
  match e with
  | BLit z => if (0 <=? z) && (z <? 2 ^ 64) then Some 64 else None
  | BVar k => Some (nth k ws 0)
  | BAnd a b => omap2 Z.min (bw a) (bw b)
  | BOr a b | BXor a b => omap2 Z.max (bw a) (bw b)
  | BShl a n => if 0 <=? n then option_map (fun w => w + n) (bw a) else None
  | BShr a n => if 0 <=? n then bw a else None
  | BWrap n _ => Some (Z.of_N n)
  | BSwrap _ _ => None
  | BAdd a b => option_map (fun w => w + 1) (omap2 Z.max (bw a) (bw b))
  end.

Fixpoint tb (e : bx) (i : Z) {struct e} : option bf :=
  match e with
  | BLit z => Some (if Z.testbit z i then FT else FF)
  | BVar k => Some (if (0 <=? i) && (i <? nth k ws 0) then FA k i else FF)
  | BAnd a b => omap2 fand (tb a i) (tb b i)
  | BOr a b => omap2 f_or (tb a i) (tb b i)
  | BXor a b => omap2 fxor (tb a i) (tb b i)
  | BShl a n => if i - n <? 0 then Some FF else tb a (i - n)
  | BShr a n => if i + n <? 0 then Some FF else tb a (i + n)
  | BWrap n a => if i <? Z.of_N n then tb a i else Some FF
  | BSwrap n a => if Z.of_N n <=? 0 then None else if i <? Z.of_N n - 1 then tb a i else tb a (Z.of_N n - 1)
  | BAdd a b =>
      match bw a, bw b with
      | Some wa, Some wb =>
          if forallb (fun j => match omap2 fand (tb a (Z.of_nat j)) (tb b (Z.of_nat j)) with
                               | Some FF => true | _ => false end) (seq 0 (Z.to_nat (Z.max wa wb)))
          then omap2 f_or (tb a i) (tb b i) else None
      | _, _ => None
      end
  end.

Lemma bound_bits : forall x w, 0 <= x -> 0 <= w -> (forall j, w <= j -> Z.testbit x j = false) -> x < 2 ^ w.
Proof.
  intros x w Hx Hw H. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.pow_pos_nonneg; lia|].
  assert (Z.log2 x < w).
  { destruct (Z.ltb_spec (Z.log2 x) w) as [|Hge]; [assumption|].
    exfalso. pose proof (Z.bit_log2 x ltac:(lia)) as Hb. rewrite (H _ Hge) in Hb. discriminate. }
  apply Z.log2_lt_pow2; lia.
Qed.

Hypothesis Henv : forall k, 0 <= nth k ws 0 /\ 0 <= nth k env 0 < 2 ^ nth k ws 0.

Lemma bw_ok : forall e w, bw e = Some w -> 0 <= w /\ 0 <= bden e < 2 ^ w.
Proof.
  induction e; cbn; intros w H.
  - destruct ((0 <=? z) && (z <? 2 ^ 64)) eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - injection H as <-. apply Henv.
  - destruct (bw e1) as [w1|], (bw e2) as [w2|]; try discriminate. injection H as <-.
    destruct (IHe1 _ eq_refl), (IHe2 _ eq_refl). split; [lia|]. split; [apply Z.land_nonneg; lia|].
    apply bound_bits; [apply Z.land_nonneg; lia|lia|]. intros j Hj. rewrite Z.land_spec.
    destruct (Z.min_spec w1 w2) as [[? E]|[? E]]; rewrite E in Hj;
      [rewrite (tb_small (bden e1) w1 j) by lia | rewrite (tb_small (bden e2) w2 j) by lia; apply andb_false_r];
      reflexivity.
  - destruct (bw e1) as [w1|], (bw e2) as [w2|]; try discriminate. injection H as <-.
    destruct (IHe1 _ eq_refl), (IHe2 _ eq_refl). split; [lia|]. split; [apply Z.lor_nonneg; lia|].
    apply bound_bits; [apply Z.lor_nonneg; lia|lia|]. intros j Hj. rewrite Z.lor_spec.
    rewrite (tb_small (bden e1) w1 j), (tb_small (bden e2) w2 j) by lia. reflexivity.
  - destruct (bw e1) as [w1|], (bw e2) as [w2|]; try discriminate. injection H as <-.
    destruct (IHe1 _ eq_refl), (IHe2 _ eq_refl). split; [lia|]. split; [apply Z.lxor_nonneg; lia|].
    apply bound_bits; [apply Z.lxor_nonneg; lia|lia|]. intros j Hj. rewrite Z.lxor_spec.
    rewrite (tb_small (bden e1) w1 j), (tb_small (bden e2) w2 j) by lia. reflexivity.
  - destruct (0 <=? n) eqn:En; [|discriminate]. apply Z.leb_le in En.
    destruct (bw e) as [w1|]; [|discriminate]. injection H as <-. destruct (IHe _ eq_refl).
    split; [lia|]. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia. nia.
  - destruct (0 <=? n) eqn:En; [|discriminate]. apply Z.leb_le in En.
    destruct (IHe _ H). split; [lia|]. rewrite Z.shiftr_div_pow2 by lia.
    split; [apply Z.div_pos; lia|]. eapply Z.le_lt_trans; [apply Z.div_le_upper_bound|]; [lia| |exact (proj2 H1)].
    pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) En). nia.
  - injection H as <-. split; [lia|]. apply bv_wrap_in_range.
  - discriminate.
  - destruct (bw e1) as [w1|], (bw e2) as [w2|]; try discriminate. injection H as <-.
    destruct (IHe1 _ eq_refl), (IHe2 _ eq_refl). split; [lia|]. rewrite Z.pow_add_r by lia.
    assert (2 ^ w1 <= 2 ^ Z.max w1 w2) by (apply Z.pow_le_mono_r; lia).
    assert (2 ^ w2 <= 2 ^ Z.max w1 w2) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma lxor_lor : forall a b, Z.land a b = 0 -> Z.lxor a b = Z.lor a b.
Proof.
  intros a b H. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.lor_spec.
  assert (Hb := f_equal (fun z => Z.testbit z i) H). cbn in Hb. rewrite Z.land_spec, Z.bits_0 in Hb.
  destruct (Z.testbit a i), (Z.testbit b i); cbn in *; congruence.
Qed.

Lemma tb_ok : forall e i f, 0 <= i -> tb e i = Some f -> Z.testbit (bden e) i = fden f.
Proof.
  induction e; cbn; intros i f Hi H.
  - injection H as <-. destruct (Z.testbit z i); reflexivity.
  - injection H as <-. destruct ((0 <=? i) && (i <? nth k ws 0)) eqn:E; [reflexivity|].
    cbn. apply tb_small with (k := nth k ws 0); [apply Henv|apply Henv|].
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E; lia|apply Z.ltb_ge in E; lia].
  - destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate. injection H as <-.
    rewrite fand_ok, Z.land_spec, (IHe1 i b), (IHe2 i b0); auto.
  - destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate. injection H as <-.
    rewrite f_or_ok, Z.lor_spec, (IHe1 i b), (IHe2 i b0); auto.
  - destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate. injection H as <-.
    rewrite fxor_ok, Z.lxor_spec, (IHe1 i b), (IHe2 i b0); auto.
  - rewrite Z.shiftl_spec by lia. destruct (i - n <? 0) eqn:E.
    + injection H as <-. apply Z.ltb_lt in E. apply Z.testbit_neg_r. lia.
    + apply Z.ltb_ge in E. apply IHe; [lia|exact H].
  - destruct (i + n <? 0) eqn:E.
    + injection H as <-. apply Z.ltb_lt in E. rewrite Z.shiftr_spec by lia. apply Z.testbit_neg_r. lia.
    + apply Z.ltb_ge in E. rewrite Z.shiftr_spec by lia. apply IHe; [lia|exact H].
  - rewrite tb_wrap by lia. destruct (i <? Z.of_N n); cbn; [apply IHe; auto|injection H as <-; reflexivity].
  - destruct (Z.of_N n <=? 0) eqn:E0; [discriminate|]. apply Z.leb_gt in E0.
    rewrite tb_swrap by lia. destruct (i <? Z.of_N n - 1) eqn:E; [apply IHe; auto|].
    apply Z.ltb_ge in E. apply IHe; [lia|exact H].
  - destruct (bw e1) as [w1|] eqn:W1, (bw e2) as [w2|] eqn:W2; try discriminate.
    destruct (forallb _ _) eqn:F; [|discriminate].
    destruct (bw_ok _ _ W1) as [Hw1 [Ha1 Ha2]], (bw_ok _ _ W2) as [Hw2 [Hb1 Hb2]].
    assert (D : Z.land (bden e1) (bden e2) = 0).
    { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.ltb_spec j (Z.max w1 w2)) as [Hl|Hl].
      - rewrite forallb_forall in F. specialize (F (Z.to_nat j) ltac:(apply in_seq; lia)).
        rewrite Z2Nat.id in F by lia.
        destruct (tb e1 j) as [g1|] eqn:G1, (tb e2 j) as [g2|] eqn:G2; cbn in F; try discriminate.
        destruct (fand g1 g2) eqn:G; try discriminate.
        rewrite (IHe1 j g1), (IHe2 j g2) by auto. rewrite <- fand_ok, G. reflexivity.
      - rewrite (tb_small (bden e1) w1 j), (tb_small (bden e2) w2 j) by lia. reflexivity. }
    rewrite (Z.add_nocarry_lxor _ _ D), (lxor_lor _ _ D).
    destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate. injection H as <-.
    rewrite f_or_ok, Z.lor_spec, (IHe1 i b), (IHe2 i b0); auto.
Qed.

Fixpoint bf_eqb (f g : bf) : bool :=
  match f, g with
  | FT, FT | FF, FF => true
  | FA k j, FA k' j' => Nat.eqb k k' && Z.eqb j j'
  | FAnd a b, FAnd a' b' | FOr a b, FOr a' b' | FXor a b, FXor a' b' => bf_eqb a a' && bf_eqb b b'
  | _, _ => false
  end.

Lemma bf_eqb_ok : forall f g, bf_eqb f g = true -> fden f = fden g.
Proof.
  induction f; destruct g; cbn; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHf1 _ H1), (IHf2 _ H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHf1 _ H1), (IHf2 _ H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHf1 _ H1), (IHf2 _ H2). reflexivity.
Qed.

Definition bits_ok (e1 e2 : bx) : bool :=
  forallb (fun i => match tb e1 (Z.of_nat i), tb e2 (Z.of_nat i) with
                    | Some f, Some g => bf_eqb f g | _, _ => false end) (seq 0 64).

Lemma bits_ok_sound : forall e1 e2, bits_ok e1 e2 = true -> bv_wrap 64 (bden e1) = bv_wrap 64 (bden e2).
Proof.
  intros e1 e2 H. apply Z.bits_inj'. intros i Hi. rewrite !tb_wrap by exact Hi.
  change (Z.of_N 64) with 64. destruct (Z.ltb_spec i 64) as [Hl|Hl]; [cbn|reflexivity].
  unfold bits_ok in H. rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia.
  destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate.
  rewrite (tb_ok e1 i b), (tb_ok e2 i b0) by auto. apply bf_eqb_ok. exact H.
Qed.
Definition bits_okn (n : nat) (e1 e2 : bx) : bool :=
  forallb (fun i => match tb e1 (Z.of_nat i), tb e2 (Z.of_nat i) with
                    | Some f, Some g => bf_eqb f g | _, _ => false end) (seq 0 n).

Lemma bits_okn_sound : forall n e1 e2, bits_okn n e1 e2 = true -> bv_wrap (N.of_nat n) (bden e1) = bv_wrap (N.of_nat n) (bden e2).
Proof.
  intros n e1 e2 H. apply Z.bits_inj'. intros i Hi. rewrite !tb_wrap by exact Hi.
  rewrite nat_N_Z. destruct (Z.ltb_spec i (Z.of_nat n)) as [Hl|Hl]; [cbn|reflexivity].
  unfold bits_okn in H. rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia.
  destruct (tb e1 i) eqn:E1, (tb e2 i) eqn:E2; try discriminate.
  rewrite (tb_ok e1 i b), (tb_ok e2 i b0) by auto. apply bf_eqb_ok. exact H.
Qed.
End Den.

(** Reification.  [vs] is the list of input variables, as a Rocq list term. *)
Ltac idx x vs :=
  lazymatch vs with
  | (x :: _)%list => constr:(O)
  | (_ :: ?r)%list => let n := idx x r in constr:(S n)
  end.

Ltac reify e vs :=
  lazymatch e with
  | Z.land ?a ?b => let x := reify a vs in let y := reify b vs in constr:(BAnd x y)
  | Z.lor ?a ?b => let x := reify a vs in let y := reify b vs in constr:(BOr x y)
  | Z.lxor ?a ?b => let x := reify a vs in let y := reify b vs in constr:(BXor x y)
  | Z.shiftl ?a ?n => let x := reify a vs in constr:(BShl x n)
  | Z.shiftr ?a ?n => let x := reify a vs in constr:(BShr x n)
  | bv_wrap ?n ?a => let x := reify a vs in constr:(BWrap n x)
  | bv_swrap ?n ?a => let x := reify a vs in constr:(BSwrap n x)
  | Z.add ?a ?b => let x := reify a vs in let y := reify b vs in constr:(BAdd x y)
  | _ => match e with
         | _ => let k := idx e vs in constr:(BVar k)
         | _ => let _ := match goal with _ => check_closed_term e end in constr:(BLit e)  (* closed only: never an open term to the vm *)
         end
  end.

(* Z_to_bv 64 L = Z_to_bv 64 R over the inputs [vs] of widths [ws], with range hypotheses [Hr]. *)
Ltac bits_with vs ws Hr :=
  v_unfold; apply bv_eq; rewrite ?Z_to_bv_unsigned;
  lazymatch goal with
  | |- bv_wrap 64 ?L = bv_wrap 64 ?R =>
      let l := reify L vs in let r := reify R vs in
      let EL := fresh "EL" in let ER := fresh "ER" in
      assert (EL : bden vs l = L) by (cbv [bden nth]; reflexivity);
      assert (ER : bden vs r = R) by (cbv [bden nth]; reflexivity);
      rewrite <- EL, <- ER; clear EL ER;
      apply (bits_ok_sound vs ws Hr); vm_compute; reflexivity
  end.

(* bv_wrap n L = bv_wrap n R for a literal width n. *)
Ltac zbits_with n vs ws Hr :=
  lazymatch goal with
  | |- bv_wrap ?nn ?L = bv_wrap ?nn ?R =>
      let l := reify L vs in let r := reify R vs in
      let EL := fresh "EL" in let ER := fresh "ER" in
      assert (EL : bden vs l = L) by (cbv [bden nth]; reflexivity);
      assert (ER : bden vs r = R) by (cbv [bden nth]; reflexivity);
      rewrite <- EL, <- ER; clear EL ER;
      change nn with (N.of_nat n);
      apply (bits_okn_sound vs ws Hr n); vm_compute; reflexivity
  end.

(** The prototype: spike 9's hardest decode field, the J-type immediate, as the compiled code computes
    it (0x3ea46-0x3ea6a), against the C's formula. *)
Section Proto.
Variables b0 b1 b2 b3 : Z.
Hypothesis H0 : 0 <= b0 < 2 ^ 8.
Hypothesis H1 : 0 <= b1 < 2 ^ 8.
Hypothesis H2 : 0 <= b2 < 2 ^ 8.
Hypothesis H3 : 0 <= b3 < 2 ^ 8.

Definition w32 : Z := Z.lor b0 (Z.lor (Z.shiftl b1 8) (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24))).
Definition bitz (w hi lo : Z) : Z := Z.land (Z.shiftr w lo) (Z.ones (hi - lo + 1)).

Lemma proto_j :
  let a2 := Z_to_bv 64 b3 in
  let a1' := v_or (v_slliw a2 24) (v_slli (Z_to_bv 64 b2) 16) in
  let t2 := v_or a1' (v_or (v_slli (Z_to_bv 64 b1) 8) (Z_to_bv 64 b0)) in
  let t1 := v_srliw a1' 20 in
  v_srai (v_slli (v_or (v_or (v_or (v_slli (v_andi a2 128) 13) (v_and t2 (v_lui 1044480))) (v_andi t1 2046))
                      (v_srli (v_slli t1 63) 52)) 43) 43
  = Z_to_bv 64 (bv_swrap 21 (Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w32 31 31) 20) (Z.shiftl (bitz w32 19 12) 12))
                                       (Z.shiftl (bitz w32 20 20) 11)) (Z.shiftl (bitz w32 30 21) 1))).
Proof.
  intros. subst a2 a1' t2 t1. unfold w32, bitz.
  assert (Hr : forall k, 0 <= nth k [8;8;8;8] 0 /\ 0 <= nth k [b0;b1;b2;b3] 0 < 2 ^ nth k [8;8;8;8] 0).
  { intros [|[|[|[|k]]]]; cbn; try lia; destruct k; cbn; lia. }
  Time bits_with constr:([b0;b1;b2;b3]) constr:([8;8;8;8]) Hr.
Qed.
End Proto.
