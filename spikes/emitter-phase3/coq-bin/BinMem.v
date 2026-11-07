(** * A chain of stores into a small struct, as one template of its bytes.

    [wtpl m o t] is memory [m] with the bytes [t] (where [Some]) at [o].  A store at [o + k] of
    bytes inside the template is an update of the template ([meq_step]), so the many stores of a
    compiled path become one list, compared with the spec's bytes ([meq_fin]).  Proof-side only. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Common Require Import PropExec CatExec MemSplit SeqExec StoreOk WxExec.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import BinRun.
Import ListNotations.
Open Scope Z_scope.

Definition mem := word -> option byte.

Lemma wbytes_at : forall bs (m : mem) (a x : word), bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  wbytes m a bs x =
  let d := bv_unsigned x - bv_unsigned a in
  if (0 <=? d) && (d <? Z.of_nat (length bs)) then Some (nth (Z.to_nat d) bs (Z_to_bv 8 0)) else m x.
Proof.
  intros bs m a x Hb. cbn zeta.
  destruct (Z.leb_spec 0 (bv_unsigned x - bv_unsigned a)), (Z.ltb_spec (bv_unsigned x - bv_unsigned a) (Z.of_nat (length bs)));
    cbn [andb]; [apply wbytes_inside; lia | apply wbytes_outside; lia..].
Qed.

Definition wtpl (m : mem) (o : word) (t : list (option byte)) : mem :=
  fun x => let d := bv_unsigned x - bv_unsigned o in
    if (0 <=? d) && (d <? Z.of_nat (length t)) then
      match nth (Z.to_nat d) t None with Some b => Some b | None => m x end
    else m x.

Definition updt (t : list (option byte)) (k : Z) (bs : list byte) : list (option byte) :=
  firstn (Z.to_nat k) t ++ map Some bs ++ skipn (Z.to_nat k + length bs)%nat t.

Lemma updt_length : forall t k bs, 0 <= k -> (Z.to_nat k + length bs <= length t)%nat ->
  length (updt t k bs) = length t.
Proof. intros. unfold updt. rewrite !length_app, length_firstn, length_map, length_skipn. lia. Qed.

Lemma nth_updt : forall t k bs j, 0 <= k -> (Z.to_nat k + length bs <= length t)%nat ->
  nth j (updt t k bs) None =
  if (j <? Z.to_nat k)%nat then nth j t None
  else if (j <? Z.to_nat k + length bs)%nat then Some (nth (j - Z.to_nat k) bs (Z_to_bv 8 0)) else nth j t None.
Proof.
  intros t k bs j Hk Hl. unfold updt.
  destruct (Nat.ltb_spec j (Z.to_nat k)).
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec j (Z.to_nat k)); [reflexivity|lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Init.Nat.min (Z.to_nat k) (length t)) with (Z.to_nat k) by lia.
    destruct (Nat.ltb_spec j (Z.to_nat k + length bs)).
    + rewrite app_nth1 by (rewrite length_map; lia).
      rewrite (nth_indep _ None (Some (Z_to_bv 8 0))) by (rewrite length_map; lia).
      rewrite map_nth. reflexivity.
    + rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, nth_skipn. f_equal. lia.
Qed.

Definition meq (m1 m2 : mem) : Prop := forall x, m1 x = m2 x.

Lemma wbytes_ext : forall bs (m1 m2 : mem) a, meq m1 m2 -> meq (wbytes m1 a bs) (wbytes m2 a bs).
Proof.
  induction bs as [|b r IH]; intros m1 m2 a H x; cbn [wbytes]; [apply H|].
  apply IH. intro y. destruct (bv_eqb y a); [reflexivity|apply H].
Qed.

Lemma meq_base : forall m o n, meq m (wtpl m o (repeat None n)).
Proof.
  intros m o n x. unfold wtpl. destruct (_ && _); [|reflexivity]. rewrite nth_repeat. reflexivity.
Qed.

Lemma meq_step : forall (M m : mem) o t k bs,
  meq M (wtpl m o t) -> 0 <= k -> (0 < length bs)%nat -> (Z.to_nat k + length bs <= length t)%nat ->
  bv_unsigned o + Z.of_nat (length t) <= 2 ^ 64 ->
  meq (wbytes M (v_addi o k) bs) (wtpl m o (updt t k bs)).
Proof.
  intros M m o t k bs H Hk Hne Hl Hb x.
  rewrite (wbytes_ext _ _ _ _ H x).
  assert (Ha : bv_unsigned (v_addi o k) = bv_unsigned o + k) by (apply u_addi; pose proof (bv_unsigned_in_range _ o); lia).
  rewrite wbytes_at by (rewrite Ha; lia). cbn zeta. rewrite Ha. unfold wtpl. rewrite updt_length by lia.
  set (d := bv_unsigned x - bv_unsigned o).
  replace (bv_unsigned x - (bv_unsigned o + k)) with (d - k) by (subst d; lia).
  destruct (Z.leb_spec 0 (d - k)), (Z.ltb_spec (d - k) (Z.of_nat (length bs))); cbn [andb].
  - destruct (Z.leb_spec 0 d), (Z.ltb_spec d (Z.of_nat (length t))); cbn [andb]; try lia.
    rewrite nth_updt by lia.
    destruct (Nat.ltb_spec (Z.to_nat d) (Z.to_nat k)); [lia|].
    destruct (Nat.ltb_spec (Z.to_nat d) (Z.to_nat k + length bs)); [|lia].
    f_equal. f_equal. lia.
  - destruct (Z.leb_spec 0 d), (Z.ltb_spec d (Z.of_nat (length t))); cbn [andb]; try reflexivity.
    rewrite nth_updt by lia.
    destruct (Nat.ltb_spec (Z.to_nat d) (Z.to_nat k)); [lia|].
    destruct (Nat.ltb_spec (Z.to_nat d) (Z.to_nat k + length bs)); [lia|reflexivity].
  - destruct (Z.leb_spec 0 d), (Z.ltb_spec d (Z.of_nat (length t))); cbn [andb]; try reflexivity.
    rewrite nth_updt by lia.
    destruct (Nat.ltb_spec (Z.to_nat d) (Z.to_nat k)); [reflexivity|lia].
  - destruct (Z.leb_spec 0 d), (Z.ltb_spec d (Z.of_nat (length t))); cbn [andb]; try reflexivity; lia.
Qed.

Lemma meq_fin : forall (M m : mem) o t bs,
  meq M (wtpl m o t) -> t = map Some bs -> bv_unsigned o + Z.of_nat (length bs) <= 2 ^ 64 ->
  meq M (wbytes m o bs).
Proof.
  intros M m o t bs H -> Hb x. rewrite H. rewrite wbytes_at by exact Hb. cbn zeta. unfold wtpl.
  rewrite length_map. destruct (_ && _) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (nth_indep _ None (Some (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth. reflexivity.
Qed.

(* Turns [meq CHAIN (wtpl m o ?t)] into the template, store by store. *)
Ltac tpl_norm :=
  lazymatch goal with
  | |- meq (wbytes ?M (v_addi ?o ?k) ?bs) _ =>
      eapply meq_step; [tpl_norm | lia | rewrite ?length_word_to_le_bytes; cbn; lia | cbn [length repeat updt firstn skipn Z.to_nat]; rewrite ?length_app, ?length_map, ?length_firstn, ?length_skipn, ?length_word_to_le_bytes; cbn; lia
                       | rewrite ?repeat_length; cbn; lia ]
  | |- meq _ _ => apply meq_base
  end.
