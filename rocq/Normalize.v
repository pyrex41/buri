(* Eliminate administrative lets by symbolic interpretation. The theorem is
   for total exact-integer expressions; effects/errors are outside this profile. *)
From Coq Require Import ZArith.
From Buri Require Import NativeArithmetic.
Module Normalize.
Inductive arithmetic :=
| Lit : Z -> arithmetic | Var : nat -> arithmetic
| Add : arithmetic -> arithmetic -> arithmetic
| Sub : arithmetic -> arithmetic -> arithmetic
| Mul : arithmetic -> arithmetic -> arithmetic.
Fixpoint denote (rho : nat -> Z) e : Z :=
 match e with
 | Lit z => z | Var i => rho i
 | Add a b => (denote rho a + denote rho b)%Z
 | Sub a b => (denote rho a - denote rho b)%Z
 | Mul a b => (denote rho a * denote rho b)%Z
 end.
Definition bind (rho : nat -> arithmetic) v i := match i with O => v | S j => rho j end.
Fixpoint symbolic rho e : arithmetic :=
 match e with
 | KLit z => Lit z | KVar i => rho i
 | KAdd a b => Add (symbolic rho a) (symbolic rho b)
 | KSub a b => Sub (symbolic rho a) (symbolic rho b)
 | KMul a b => Mul (symbolic rho a) (symbolic rho b)
 | KLet a b => symbolic (bind rho (symbolic rho a)) b
 end.
Theorem symbolic_preserves : forall e valuation symbolic_env concrete_env,
 (forall i, denote valuation (symbolic_env i) = concrete_env i) ->
 denote valuation (symbolic symbolic_env e) = keval concrete_env e.
Proof.
 induction e; intros valuation symbolic_env concrete_env Agree; simpl; try reflexivity.
 - apply Agree.
 - rewrite (IHe1 _ _ _ Agree), (IHe2 _ _ _ Agree); reflexivity.
 - rewrite (IHe1 _ _ _ Agree), (IHe2 _ _ _ Agree); reflexivity.
 - rewrite (IHe1 _ _ _ Agree), (IHe2 _ _ _ Agree); reflexivity.
 - apply IHe2. intros [|i]; simpl; [apply IHe1 | apply Agree]; exact Agree.
Qed.
Definition normalize e := symbolic Var e.
Corollary normalize_preserves : forall e rho, denote rho (normalize e) = keval rho e.
Proof. intros; apply symbolic_preserves; reflexivity. Qed.
Fixpoint arithmetic_eq_dec (a b : arithmetic) : {a=b}+{a<>b}.
Proof. decide equality; try apply Z.eq_dec; try apply Nat.eq_dec. Defined.
Theorem normal_equal_sound : forall a b,
 normalize a = normalize b -> forall rho, keval rho a = keval rho b.
Proof. intros a b H rho. rewrite <- !normalize_preserves, H; reflexivity. Qed.
End Normalize.
