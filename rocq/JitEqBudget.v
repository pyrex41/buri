(* JitLowerEquiv.eq_budget_statement is false: past the budget S (length h), more budget can
   still change what = answers, here from None to Some false.

   The statement quantifies over every profile P', and a profile's equality on inexact numbers
   (inexact_cmp P' PEqual) is any boolean function. `tol` below takes it to be a tolerance,
   |x - y| <= 1 on float bit patterns: reflexive and symmetric, but not transitive (0 ~ 1 and
   1 ~ 2, but not 0 ~ 2).

   The heap has five cells. Each holds a number and a pointer, so = compares the two numbers
   and then follows the two pointers:
     0 : [0; ->3]    3 : [2; ->0]      (a 2-cycle)
     1 : [1; ->2]    2 : [1; ->4]    4 : [2; ->1]      (a 3-cycle)
   Comparing cells 1 and 3 walks through the pairs (1,3) (2,0) (4,3) (1,0) (2,3) (4,0). The labels
   agree under `tol` until (4,0) compares 2 with 0. Six pairs need budget 7, but
   kl_eq_r's budget is S 5 = 6. With a transitive equality, Moore's bound applies to this
   functional walk: labels that agree with a common label agree with each other. Without
   transitivity, the walk around two coprime cycles can run up to their product. *)
From Coq Require Import List ZArith NArith Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitProfile JitLowerEquiv.
Import ListNotations.
Module JitEqBudget.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 KLPort.KLPort JitProfile.JitProfile.

Definition tol_cmp (_ : prim) (a b : num) : bool := match a, b with
 | NFloat x, NFloat y => (N.leb x (y + 1) && N.leb y (x + 1))%bool
 | _, _ => false end.

Definition tol : profile := Profile
 (inexact_op jit_profile) tol_cmp (int_div_inexact jit_profile) (float_text jit_profile)
 (str_other jit_profile) (sys_message jit_profile) (absvector_fill jit_profile)
 (time_value jit_profile) (stack_limit jit_profile) (heap_limit jit_profile).

Definition cell (label : N) (next : nat) : list value := [VNum (NFloat label); VVec next].
Definition h5 : list (list value) := [cell 0 3; cell 1 2; cell 1 4; cell 2 0; cell 2 1].

Lemma h5_ok : Forall (lok (List.length h5)) h5.
Proof. repeat constructor; cbn; lia. Qed.

(* The answers at budgets 6 and 7. Neither depends on the port rules: no closure is compared. *)
Lemma at_budget_6 : forall R, eq_depth_r R tol h5 6 (VVec 1) (VVec 3) = None.
Proof. intro R. vm_compute. reflexivity. Qed.
Lemma at_budget_7 : forall R, eq_depth_r R tol h5 7 (VVec 1) (VVec 3) = Some false.
Proof. intro R. vm_compute. reflexivity. Qed.
Lemma kl_eq_h5 : forall R, kl_eq_r R tol h5 (VVec 1) (VVec 3) = None.
Proof. intro R. exact (at_budget_6 R). Qed.

Theorem eq_budget_refuted : forall sealed, ~ JitLowerEquiv.eq_budget_statement sealed.
Proof.
 intros sealed H.
 specialize (H tol h5 7 (VVec 1) (VVec 3) h5_ok).
 assert (E : eq_depth_r (jit_rules sealed) tol h5 7 (VVec 1) (VVec 3) =
             kl_eq_r (jit_rules sealed) tol h5 (VVec 1) (VVec 3))
   by (apply H; cbn; lia).
 rewrite at_budget_7, kl_eq_h5 in E. discriminate E.
Qed.

(* What does hold for every profile: more budget never takes back a defined answer. It cannot
   turn Some into None or change which Some, because an answer is defined only if every
   comparison it reads is defined. So if the side with fewer cells answers Some, the other side,
   with more cells and so more budget, gives the same answer. The other direction fails: a
   None at the smaller budget can become Some at the larger one. *)
Lemma list_eq_mono : forall (f g : value -> value -> option bool),
 (forall u v y, f u v = Some y -> g u v = Some y) ->
 forall xs ys y, list_eq f xs ys = Some y -> list_eq g xs ys = Some y.
Proof.
 intros f g Hfg. induction xs as [|u xs IH]; intros [|v ys] y H; cbn in *; try exact H.
 destruct (f u v) as [[|]|] eqn:E; try discriminate H.
 - rewrite (Hfg _ _ _ E). exact (IH _ _ H).
 - rewrite (Hfg _ _ _ E). exact H.
Qed.

Lemma eq_depth_mono : forall R P h d a b y,
 eq_depth_r R P h d a b = Some y -> eq_depth_r R P h (S d) a b = Some y.
Proof.
 intros R P h. induction d as [|d IHd]; intros a b y H; [discriminate H|].
 revert b y H.
 induction a as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex]; intros w y H;
  destruct w as [n'|s'|bb'|t'| |b1 b2|l0|st'|x1 e2 r2|e3 r3|f1 args1|ex']; try exact H.
 - (* VCons *)
   change (match eq_depth_r R P h (S d) a1 b1 with Some true => eq_depth_r R P h (S d) a2 b2 | r => r end
           = Some y) in H.
   change (match eq_depth_r R P h (S (S d)) a1 b1 with Some true => eq_depth_r R P h (S (S d)) a2 b2 | r => r end
           = Some y).
   destruct (eq_depth_r R P h (S d) a1 b1) as [[|]|] eqn:E; try discriminate H.
   + rewrite (IHa1 _ _ E). exact (IHa2 _ _ H).
   + rewrite (IHa1 _ _ E). exact H.
 - (* VVec *)
   cbn in H |- *. destruct (Nat.eqb l l0); [exact H|].
   destruct (nth_error h l), (nth_error h l0); try discriminate H.
   exact (list_eq_mono _ _ IHd _ _ _ H).
Qed.

Lemma eq_depth_mono_le : forall R P h d d' a b y, (d <= d')%nat ->
 eq_depth_r R P h d a b = Some y -> eq_depth_r R P h d' a b = Some y.
Proof. intros R P h d d' a b y L. induction L; intro H; [exact H|]. apply eq_depth_mono. auto. Qed.

End JitEqBudget.
