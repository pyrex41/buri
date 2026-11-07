(** * Shared by the decode and run_block proofs: exhaustive checks over bytes, and the shape of
    [decode]'s postcondition. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import base decidable bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Common Require Import PropExec CatExec.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import BinMem DecSpec.
Import ListNotations.
Open Scope Z_scope.

(** Exhaustive checks over one and two bytes, counting in [Z] (a [seq] of unary [nat]s would make
    the vm's conversions quadratic). *)
Fixpoint zall (k : nat) (z : Z) (f : Z -> bool) : bool :=
  match k with O => true | S k' => f z && zall k' (z + 1) f end.

Lemma zall_ok : forall k z f, zall k z f = true -> forall x, z <= x < z + Z.of_nat k -> f x = true.
Proof.
  induction k as [|k IH]; intros z f H x Hx; cbn [zall] in H; [lia|].
  apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec x z) as [->|Hne]; [exact H1|].
  apply (IH (z + 1) f H2). lia.
Qed.

Lemma enum1 : forall (P : Z -> Prop) (D : forall x, Decision (P x)),
  zall 256 0 (fun x => bool_decide (P x)) = true -> forall x, 0 <= x < 256 -> P x.
Proof. intros P D H x Hx. exact (bool_decide_eq_true_1 (P x) (zall_ok _ _ _ H x ltac:(cbn; lia))). Qed.

Lemma enum2 : forall (P : Z -> Z -> Prop) (D : forall x y, Decision (P x y)),
  zall 256 0 (fun x => zall 256 0 (fun y => bool_decide (P x y))) = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> P x y.
Proof.
  intros P D H x y Hx Hy. pose proof (zall_ok _ _ _ H x ltac:(cbn; lia)) as H1. cbv beta in H1.
  exact (bool_decide_eq_true_1 (P x y) (zall_ok _ _ _ H1 y ltac:(cbn; lia))).
Qed.

(** The same with a boolean built by hand: nested [if]s are lazy in the vm, where a [Decision]
    instance for an implication evaluates both sides. *)
Lemma enum2b : forall (P : Z -> Z -> Prop) (f : Z -> Z -> bool),
  (forall x y, f x y = true -> P x y) ->
  zall 256 0 (fun x => zall 256 0 (fun y => f x y)) = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> P x y.
Proof.
  intros P f Hf H x y Hx Hy. apply Hf. pose proof (zall_ok _ _ _ H x ltac:(cbn; lia)) as H1. cbv beta in H1.
  exact (zall_ok _ _ _ H1 y ltac:(cbn; lia)).
Qed.

Lemma impl_step : forall (L b q : bool) (Q : Prop), (q = true -> Q) -> (if Bool.eqb L b then q else true) = true -> L = b -> Q.
Proof. intros L b q Q H E Hl. subst L. rewrite eqb_reflx in E. exact (H E). Qed.

Ltac boolify P :=
  lazymatch P with
  | (?L = ?b) -> ?Q => let q := boolify Q in constr:(if Bool.eqb L b then q else true)
  | ?T = ?U => constr:(bool_decide (T = U))
  end.

Ltac impl_chain :=
  first [ let Hq := fresh "Hq" in intro Hq; refine (impl_step _ _ _ _ _ Hq); impl_chain
        | let Hq := fresh "Hq" in intro Hq; exact (bool_decide_eq_true_1 _ Hq) ].

Definition dkept (x : reg) : Prop :=
  x <> 5%bv /\ x <> 6%bv /\ x <> 7%bv /\ x <> 11%bv /\ x <> 12%bv /\ x <> 13%bv /\ x <> 14%bv /\
  x <> 15%bv /\ x <> 16%bv /\ x <> 17%bv /\ x <> 28%bv /\ x <> 29%bv /\ x <> 30%bv.

Definition dpost (R0 : bvmap 5 word) (mem0 : mem) (i : ins) (regs : bvmap 5 word) (m : mem) : Prop :=
  (forall x, dkept x -> getr regs x = getr R0 x) /\ meq m (wbytes mem0 (getr R0 10) (encb i)).

