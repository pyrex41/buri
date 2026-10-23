(* Generated from the loaded Shen equation theory and theorem statements. *)
From Buri Require Import Arithmetic.
Lemma equation_0 : forall (v_y : nat), (nadd O v_y) = v_y.
Proof. reflexivity. Qed.
Lemma equation_1 : forall (v_x : nat) (v_y : nat), (nadd (S v_x) v_y) = (S (nadd v_x v_y)).
Proof. reflexivity. Qed.
Lemma equation_2 : forall (v_y : nat), (nmul O v_y) = O.
Proof. reflexivity. Qed.
Lemma equation_3 : forall (v_x : nat) (v_y : nat), (nmul (S v_x) v_y) = (nadd v_y (nmul v_x v_y)).
Proof. reflexivity. Qed.
Lemma equation_4 : forall (v_n : nat), (eval (Lit v_n)) = v_n.
Proof. reflexivity. Qed.
Lemma equation_5 : forall (v_a : expr) (v_b : expr), (eval (Add v_a v_b)) = (nadd (eval v_a) (eval v_b)).
Proof. reflexivity. Qed.
Lemma equation_6 : forall (v_a : expr) (v_b : expr), (eval (Mul v_a v_b)) = (nmul (eval v_a) (eval v_b)).
Proof. reflexivity. Qed.
Lemma equation_7 : forall (v_n : nat) (v_k : code), (compile (Lit v_n) v_k) = (Push v_n v_k).
Proof. reflexivity. Qed.
Lemma equation_8 : forall (v_a : expr) (v_b : expr) (v_k : code), (compile (Add v_a v_b) v_k) = (compile v_a (compile v_b (Plus v_k))).
Proof. reflexivity. Qed.
Lemma equation_9 : forall (v_a : expr) (v_b : expr) (v_k : code), (compile (Mul v_a v_b) v_k) = (compile v_a (compile v_b (Times v_k))).
Proof. reflexivity. Qed.
Lemma equation_10 : forall (v_s : stack), (run Halt v_s) = (Ok v_s).
Proof. reflexivity. Qed.
Lemma equation_11 : forall (v_n : nat) (v_k : code) (v_s : stack), (run (Push v_n v_k) v_s) = (run v_k (cons v_n v_s)).
Proof. reflexivity. Qed.
Lemma equation_12 : forall (v_k : code) (v_x : nat) (v_y : nat) (v_s : stack), (run (Plus v_k) (cons v_y (cons v_x v_s))) = (run v_k (cons (nadd v_x v_y) v_s)).
Proof. reflexivity. Qed.
Lemma equation_13 : forall (v_k : code) (v_x : nat) (v_y : nat) (v_s : stack), (run (Times v_k) (cons v_y (cons v_x v_s))) = (run v_k (cons (nmul v_x v_y) v_s)).
Proof. reflexivity. Qed.
Lemma equation_14 : forall (v_k : code), (run (Plus v_k) nil) = Fault.
Proof. reflexivity. Qed.
Lemma equation_15 : forall (v_k : code) (v_x : nat), (run (Plus v_k) (cons v_x nil)) = Fault.
Proof. reflexivity. Qed.
Lemma equation_16 : forall (v_k : code), (run (Times v_k) nil) = Fault.
Proof. reflexivity. Qed.
Lemma equation_17 : forall (v_k : code) (v_x : nat), (run (Times v_k) (cons v_x nil)) = Fault.
Proof. reflexivity. Qed.
Theorem exported_compiler_continuation : forall (v_e : expr) (v_k : code) (v_s : stack), (run (compile v_e v_k) v_s) = (run v_k (cons (eval v_e) v_s)).
Proof. apply compiler_continuation. Qed.
Theorem exported_compiler_result : forall (v_e : expr) (v_s : stack), (run (compile v_e Halt) v_s) = (Ok (cons (eval v_e) v_s)).
Proof. apply compiler_result. Qed.
