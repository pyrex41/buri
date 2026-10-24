(* The unrestricted mathematical byte theorem does not assert unrestricted
   host division correctness. Record the finite domain needed by strings. *)
From Coq Require Import List Arith Ascii Lia.
From Buri Require Import Encoder.
Import ListNotations.
Module ByteDomain.
Fixpoint calls n count : list (nat * nat) :=
 (n,count) :: match count with 0 => [] | S k => calls (Nat.div2 n) k end.
Theorem calls_bounded : forall count n bound,
 n < bound -> Forall (fun p => fst p < bound /\ snd p <= count) (calls n count).
Proof.
 induction count as [|count IH]; intros n bound H; cbn [calls]; constructor.
 - cbn; lia.
 - constructor.
 - cbn; lia.
 - eapply Forall_impl with (P := fun p : nat * nat => fst p < bound /\ snd p <= count).
   2: { apply IH. destruct n; [cbn; lia | pose proof (Nat.le_div2 n); lia]. }
   intros [a b] [A B]; cbn in *; split; [exact A|lia].
Qed.
Theorem string_byte_domain : forall c,
 Forall (fun p => fst p < 256 /\ snd p <= 8) (calls (nat_of_ascii c) 8).
Proof. intros c; apply calls_bounded, nat_ascii_bounded. Qed.
End ByteDomain.
