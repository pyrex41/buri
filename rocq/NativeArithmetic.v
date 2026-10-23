(* Translation-validation target for actual Shen-Scheme output. This is a pure
   exact-integer fragment of KLambda and Scheme, not their full semantics. *)
From Coq Require Import ZArith.
Open Scope Z_scope.
Inductive kexpr :=
| KLit : Z -> kexpr | KVar : nat -> kexpr
| KAdd : kexpr -> kexpr -> kexpr | KSub : kexpr -> kexpr -> kexpr
| KMul : kexpr -> kexpr -> kexpr | KLet : kexpr -> kexpr -> kexpr.
Inductive sexpr :=
| SLit : Z -> sexpr | SVar : nat -> sexpr
| SAdd : sexpr -> sexpr -> sexpr | SSub : sexpr -> sexpr -> sexpr
| SMul : sexpr -> sexpr -> sexpr | SLet : sexpr -> sexpr -> sexpr.
Definition extend (rho : nat -> Z) (v : Z) i :=
 match i with O => v | S j => rho j end.
Fixpoint keval (rho : nat -> Z) (e : kexpr) : Z :=
 match e with
 | KLit n => n | KVar i => rho i
 | KAdd a b => keval rho a + keval rho b
 | KSub a b => keval rho a - keval rho b
 | KMul a b => keval rho a * keval rho b
 | KLet a b => keval (extend rho (keval rho a)) b
 end.
Fixpoint seval (rho : nat -> Z) (e : sexpr) : Z :=
 match e with
 | SLit n => n | SVar i => rho i
 | SAdd a b => seval rho a + seval rho b
 | SSub a b => seval rho a - seval rho b
 | SMul a b => seval rho a * seval rho b
 | SLet a b => seval (extend rho (seval rho a)) b
 end.
(* A separate reference lowering, proved generically. NativeOutput.v validates
   actual compiler output against keval directly; it does not assume the port
   executes this reference lowering. *)
Fixpoint lower (e : kexpr) : sexpr :=
 match e with
 | KLit n => SLit n | KVar i => SVar i
 | KAdd a b => SAdd (lower a) (lower b)
 | KSub a b => SSub (lower a) (lower b)
 | KMul a b => SMul (lower a) (lower b)
 | KLet a b => SLet (lower a) (lower b)
 end.
Theorem lower_preserves : forall e rho, seval rho (lower e) = keval rho e.
Proof. induction e; intros; simpl; try reflexivity;
 rewrite IHe1, IHe2; reflexivity. Qed.
Print Assumptions lower_preserves.
