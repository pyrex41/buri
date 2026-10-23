(* Pure lexical KLambda fragment, using de Bruijn variables and exact integers.
   This formal model is not yet related by proof to shen/klambda.shen. *)
From Coq Require Import List ZArith.
Import ListNotations.
Module Lexical.
Inductive term :=
| Lit : Z -> term | Bool : bool -> term | Var : nat -> term
| Lam : term -> term | App : term -> term -> term
| LetIn : term -> term -> term | If : term -> term -> term -> term
| Add : term -> term -> term.
Inductive value := Int : Z -> value | Boolean : bool -> value
                 | Closure : term -> list value -> value.
Inductive error := Unbound | NotCallable | NotBoolean | NotInteger.
Inductive outcome := Returned : value -> outcome | Raised : error -> outcome.
Fixpoint eval (fuel : nat) (env : list value) (e : term) : option outcome :=
 match fuel with
 | O => None
 | S n =>
   match e with
   | Lit z => Some (Returned (Int z))
   | Bool b => Some (Returned (Boolean b))
   | Var i => match nth_error env i with Some v => Some (Returned v) | None => Some (Raised Unbound) end
   | Lam b => Some (Returned (Closure b env))
   | App f a =>
     match eval n env f with
     | Some (Returned vf) =>
       match eval n env a with
       | Some (Returned va) =>
         match vf with
         | Closure body captured => eval n (va :: captured) body
         | _ => Some (Raised NotCallable)
         end
       | other => other
       end
     | other => other
     end
   | LetIn a b =>
     match eval n env a with
     | Some (Returned v) => eval n (v :: env) b
     | other => other
     end
   | If c a b =>
     match eval n env c with
     | Some (Returned (Boolean true)) => eval n env a
     | Some (Returned (Boolean false)) => eval n env b
     | Some (Returned _) => Some (Raised NotBoolean)
     | other => other
     end
   | Add a b =>
     match eval n env a with
     | Some (Returned va) =>
       match eval n env b with
       | Some (Returned vb) =>
         match va, vb with
         | Int x, Int y => Some (Returned (Int (x + y)))
         | _, _ => Some (Raised NotInteger)
         end
       | other => other
       end
     | other => other
     end
   end
 end.

Theorem fuel_step : forall n env e r,
 eval n env e = Some r -> eval (S n) env e = Some r.
Proof.
 induction n as [|n IH]; intros env e r H; [discriminate|].
 destruct e; cbn in H; remember (S n) as m eqn:Em; cbn; try exact H.
 - destruct (eval n env e1) as [q|] eqn:E; try discriminate.
   rewrite (IH _ _ _ E). destruct q as [v|err]; try exact H.
   destruct (eval n env e2) as [q|] eqn:E2; try discriminate.
   rewrite (IH _ _ _ E2). destruct q as [w|err]; try exact H.
   destruct v; try exact H. apply IH; exact H.
 - destruct (eval n env e1) as [q|] eqn:E; try discriminate.
   rewrite (IH _ _ _ E). destruct q; try exact H. apply IH; exact H.
 - destruct (eval n env e1) as [q|] eqn:E; try discriminate.
   rewrite (IH _ _ _ E). destruct q as [v|err]; try exact H.
   destruct v; try exact H. destruct b; apply IH; exact H.
 - destruct (eval n env e1) as [q|] eqn:E; try discriminate.
   rewrite (IH _ _ _ E). destruct q as [v|err]; try exact H.
   destruct (eval n env e2) as [q|] eqn:E2; try discriminate.
   rewrite (IH _ _ _ E2). destruct q as [w|err]; try exact H.
Qed.
Theorem fuel_monotone : forall n m, n <= m -> forall env e r,
 eval n env e = Some r -> eval m env e = Some r.
Proof.
 intros n m Hle; induction Hle; intros; auto.
 apply fuel_step; apply IHHle; assumption.
Qed.
Definition evaluates env e r := exists fuel, eval fuel env e = Some r.
Theorem evaluation_deterministic : forall env e r1 r2,
 evaluates env e r1 -> evaluates env e r2 -> r1 = r2.
Proof.
 intros env e r1 r2 [n Hn] [m Hm].
 pose proof (fuel_monotone n (Nat.max n m) (Nat.le_max_l _ _) env e r1 Hn).
 pose proof (fuel_monotone m (Nat.max n m) (Nat.le_max_r _ _) env e r2 Hm).
 congruence.
Qed.
(* The let-to-lambda lowering recommended by the Shen porting guide.
   This theorem covers every environment, body, argument, and modeled outcome. *)
Lemma let_lowering_fuel : forall n env a b,
 eval (S (S n)) env (LetIn a b) = eval (S (S n)) env (App (Lam b) a).
Proof. reflexivity. Qed.
Theorem let_lowering : forall env a b r,
 evaluates env (LetIn a b) r <-> evaluates env (App (Lam b) a) r.
Proof.
 intros env a b r; split; intros [n H]; exists (S (S n)).
 - rewrite <- let_lowering_fuel. apply fuel_step; apply fuel_step; exact H.
 - rewrite let_lowering_fuel. apply fuel_step; apply fuel_step; exact H.
Qed.
Example lexical_capture :
 eval 20 []
  (LetIn (Lit 10)
   (LetIn (Lam (Add (Var 1) (Var 0)))
    (LetIn (Lit 99) (App (Var 1) (Lit 2))))) = Some (Returned (Int 12)).
Proof. reflexivity. Qed.
Example exhausted_is_not_error : eval 0 [] (Lit 1) = None.
Proof. reflexivity. Qed.
Example wrong_type_is_error : eval 10 [] (App (Lit 1) (Lit 2)) = Some (Raised NotCallable).
Proof. reflexivity. Qed.
End Lexical.
Print Assumptions Lexical.fuel_monotone.
Print Assumptions Lexical.evaluation_deterministic.
