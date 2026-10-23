(* Independent foundational model. No axioms, admitted proofs, extraction, or
   native computation trusted by the kernel. Compatible with Coq 8.18. *)
From Coq Require Import List Arith.
Import ListNotations.

Inductive expr : Type :=
| Lit : nat -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.
Inductive code : Type :=
| Halt : code
| Push : nat -> code -> code
| Plus : code -> code
| Times : code -> code.
Definition stack := list nat.
Inductive outcome : Type := Ok : stack -> outcome | Fault : outcome.

Fixpoint nadd (x y : nat) : nat :=
  match x with O => y | S x' => S (nadd x' y) end.
Fixpoint nmul (x y : nat) : nat :=
  match x with O => O | S x' => nadd y (nmul x' y) end.
Fixpoint eval (e : expr) : nat :=
  match e with
  | Lit n => n | Add a b => nadd (eval a) (eval b)
  | Mul a b => nmul (eval a) (eval b)
  end.
Fixpoint compile (e : expr) (k : code) : code :=
  match e with
  | Lit n => Push n k
  | Add a b => compile a (compile b (Plus k))
  | Mul a b => compile a (compile b (Times k))
  end.
Fixpoint run (k : code) (s : stack) : outcome :=
  match k with
  | Halt => Ok s
  | Push n k' => run k' (n :: s)
  | Plus k' => match s with y :: x :: rest => run k' (nadd x y :: rest) | _ => Fault end
  | Times k' => match s with y :: x :: rest => run k' (nmul x y :: rest) | _ => Fault end
  end.

Theorem nadd_standard : forall x y, nadd x y = x + y.
Proof. induction x; intros; simpl; congruence. Qed.
Theorem nmul_standard : forall x y, nmul x y = x * y.
Proof. induction x; intros; simpl.
- reflexivity.
- rewrite nadd_standard, IHx. reflexivity.
Qed.

(* Generalized continuation and stack are essential induction parameters. *)
Theorem compiler_continuation : forall e k s,
  run (compile e k) s = run k (eval e :: s).
Proof.
  induction e; intros k s; simpl.
  - reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.
Theorem compiler_result : forall e s,
  run (compile e Halt) s = Ok (eval e :: s).
Proof. intros; rewrite compiler_continuation; reflexivity. Qed.
Corollary compiler_no_stack_fault : forall e s,
  run (compile e Halt) s <> Fault.
Proof. intros e s; rewrite compiler_result; discriminate. Qed.

(* Relational semantics supplies an independently stated behavior relation. *)
Inductive evaluates : expr -> nat -> Prop :=
| eval_lit : forall n, evaluates (Lit n) n
| eval_add : forall a b x y,
    evaluates a x -> evaluates b y -> evaluates (Add a b) (nadd x y)
| eval_mul : forall a b x y,
    evaluates a x -> evaluates b y -> evaluates (Mul a b) (nmul x y).
Theorem evaluation_sound : forall e, evaluates e (eval e).
Proof. induction e; simpl; constructor; assumption. Qed.
Theorem evaluation_complete : forall e n, evaluates e n -> eval e = n.
Proof. intros e n H; induction H; simpl; congruence. Qed.
Theorem evaluation_deterministic : forall e a b,
  evaluates e a -> evaluates e b -> a = b.
Proof. intros e a b Ha Hb; pose proof (evaluation_complete _ _ Ha);
  pose proof (evaluation_complete _ _ Hb); congruence. Qed.
Theorem compiler_relational : forall e n s,
  evaluates e n -> run (compile e Halt) s = Ok (n :: s).
Proof. intros; rewrite compiler_result, (evaluation_complete _ _ H); reflexivity. Qed.

Print Assumptions compiler_continuation.
Print Assumptions compiler_result.
Print Assumptions compiler_no_stack_fault.
Print Assumptions evaluation_deterministic.
Print Assumptions compiler_relational.
