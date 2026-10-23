(* Named lexical arithmetic and a proved, shadowing-aware resolver. *)
From Coq Require Import List String ZArith.
From Buri Require Import NativeArithmetic.
Import ListNotations.
Open Scope Z_scope.
Module Resolve.
Inductive named :=
| Num : Z -> named | Name : string -> named
| Plus : named -> named -> named | Minus : named -> named -> named
| Times : named -> named -> named | Let : string -> named -> named -> named.
Definition update (env : string -> Z) x v y := if string_dec y x then v else env y.
Fixpoint meaning (env : string -> Z) e : Z :=
 match e with
 | Num z => z | Name x => env x
 | Plus a b => meaning env a + meaning env b
 | Minus a b => meaning env a - meaning env b
 | Times a b => meaning env a * meaning env b
 | Let x a b => meaning (update env x (meaning env a)) b
 end.
Fixpoint lookup x (scope : list string) : option nat :=
 match scope with
 | [] => None
 | y::rest => if string_dec x y then Some O
              else match lookup x rest with Some i => Some (S i) | None => None end
 end.
Fixpoint resolve scope e : option kexpr :=
 match e with
 | Num z => Some (KLit z)
 | Name x => match lookup x scope with Some i => Some (KVar i) | None => None end
 | Plus a b => match resolve scope a, resolve scope b with Some x,Some y => Some (KAdd x y) | _,_ => None end
 | Minus a b => match resolve scope a, resolve scope b with Some x,Some y => Some (KSub x y) | _,_ => None end
 | Times a b => match resolve scope a, resolve scope b with Some x,Some y => Some (KMul x y) | _,_ => None end
 | Let x a b => match resolve scope a, resolve (x::scope) b with Some av,Some bv => Some (KLet av bv) | _,_ => None end
 end.
Definition corresponds scope (env : string -> Z) (rho : nat -> Z) := forall x i, lookup x scope = Some i -> rho i = env x.
Lemma extend_corresponds : forall scope env rho x v,
 corresponds scope env rho -> corresponds (x::scope) (update env x v) (extend rho v).
Proof.
 intros scope env rho x v H y i E. cbn in E.
 unfold update. destruct (string_dec y x) as [Eq|Neq]; subst.
 - destruct (string_dec x x); try contradiction. inversion E; reflexivity.
 - destruct (lookup y scope) as [j|] eqn:F; try discriminate.
   inversion E; subst. cbn [extend]. apply H; exact F.
Qed.
Theorem resolve_preserves : forall n scope e,
 resolve scope n = Some e -> forall env rho,
 corresponds scope env rho -> keval rho e = meaning env n.
Proof.
 induction n; intros scope e H env rho HC; cbn in H.
 - inversion H; reflexivity.
 - destruct (lookup s scope) as [i|] eqn:E; try discriminate.
   inversion H; subst. simpl. apply HC; exact E.
 - destruct (resolve scope n1) as [a|] eqn:A; try discriminate.
   destruct (resolve scope n2) as [b|] eqn:B; try discriminate.
   inversion H; subst. simpl. rewrite (IHn1 _ _ A _ _ HC), (IHn2 _ _ B _ _ HC); reflexivity.
 - destruct (resolve scope n1) as [a|] eqn:A; try discriminate.
   destruct (resolve scope n2) as [b|] eqn:B; try discriminate.
   inversion H; subst. simpl. rewrite (IHn1 _ _ A _ _ HC), (IHn2 _ _ B _ _ HC); reflexivity.
 - destruct (resolve scope n1) as [a|] eqn:A; try discriminate.
   destruct (resolve scope n2) as [b|] eqn:B; try discriminate.
   inversion H; subst. simpl. rewrite (IHn1 _ _ A _ _ HC), (IHn2 _ _ B _ _ HC); reflexivity.
 - destruct (resolve scope n1) as [a|] eqn:A; try discriminate.
   destruct (resolve (s::scope) n2) as [b|] eqn:B; try discriminate.
   inversion H; subst. simpl. rewrite (IHn1 _ _ A _ _ HC).
   eapply IHn2; [exact B | apply extend_corresponds; exact HC].
Qed.
Lemma lookup_nth : forall scope x i, lookup x scope = Some i -> nth_error scope i = Some x.
Proof.
 induction scope; intros x i H; [discriminate|]. cbn in H.
 destruct (string_dec x a); subst.
 - inversion H; reflexivity.
 - destruct (lookup x scope) as [j|] eqn:E; try discriminate.
   inversion H; subst. simpl. apply IHscope; exact E.
Qed.
Definition valuation scope (env : string -> Z) i :=
 match nth_error scope i with Some x => env x | None => 0 end.
Lemma valuation_corresponds : forall scope env, corresponds scope env (valuation scope env).
Proof. intros scope env x i H; unfold valuation. rewrite (lookup_nth _ _ _ H). reflexivity. Qed.
Corollary resolve_named_meaning : forall n scope e env,
 resolve scope n = Some e -> keval (valuation scope env) e = meaning env n.
Proof. intros; eapply resolve_preserves; [eassumption|apply valuation_corresponds]. Qed.
Theorem resolved_equal_sound : forall scope a b e,
 resolve scope a = Some e -> resolve scope b = Some e ->
 forall env, meaning env a = meaning env b.
Proof.
 intros scope a b e A B env.
 rewrite <- (resolve_named_meaning _ _ _ env A), <- (resolve_named_meaning _ _ _ env B).
 reflexivity.
Qed.
End Resolve.
