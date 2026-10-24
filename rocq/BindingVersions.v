(* Abstract version vectors, not a refinement proof of native procedure identity. *)
From Coq Require Import List Arith ListDec.
Module BindingVersions.
Definition current (sealed live : list nat) :=
 if list_eq_dec Nat.eq_dec sealed live then true else false.
Theorem current_exact : forall sealed live, current sealed live = true <-> sealed = live.
Proof. intros; unfold current; destruct (list_eq_dec Nat.eq_dec sealed live); intuition discriminate. Qed.
Theorem current_covers : forall sealed live, current sealed live = true ->
 forall i, nth_error sealed i = nth_error live i.
Proof. intros sealed live H; apply current_exact in H; subst; auto. Qed.
Theorem changed_rejected : forall sealed live i a b,
 nth_error sealed i = Some a -> nth_error live i = Some b -> a <> b -> current sealed live = false.
Proof.
 intros sealed live i a b A B N. unfold current.
 destruct (list_eq_dec Nat.eq_dec sealed live); [subst; congruence | reflexivity].
Qed.
End BindingVersions.
