(* Generated from pinned Shen-Scheme compiler output. *)
From Coq Require Import ZArith.
From Buri Require Import NativeArithmetic.
Open Scope Z_scope.
Theorem native_schema_0 : forall rho, keval rho (KAdd (KVar 0) (KVar 1)) = seval rho (SAdd (SVar 0) (SVar 1)).
Proof. reflexivity. Qed.
Print Assumptions native_schema_0.
Theorem native_schema_1 : forall rho, keval rho (KSub (KVar 0) (KVar 1)) = seval rho (SSub (SVar 0) (SVar 1)).
Proof. reflexivity. Qed.
Print Assumptions native_schema_1.
Theorem native_schema_2 : forall rho, keval rho (KMul (KVar 0) (KVar 1)) = seval rho (SMul (SVar 0) (SVar 1)).
Proof. reflexivity. Qed.
Print Assumptions native_schema_2.
Theorem native_schema_3 : forall rho, keval rho (KAdd (KMul (KVar 0) (KVar 1)) (KSub (KVar 2) (KLit (3)))) = seval rho (SLet (SMul (SVar 0) (SVar 1)) (SAdd (SVar 0) (SSub (SVar 3) (SLit (3))))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_3.
Theorem native_schema_4 : forall rho, keval rho (KLet (KAdd (KVar 0) (KLit (1))) (KMul (KVar 0) (KVar 2))) = seval rho (SLet (SAdd (SVar 0) (SLit (1))) (SMul (SVar 0) (SVar 2))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_4.
Theorem native_schema_5 : forall rho, keval rho (KLet (KAdd (KVar 0) (KLit (1))) (KSub (KVar 0) (KVar 2))) = seval rho (SLet (SAdd (SVar 0) (SLit (1))) (SSub (SVar 0) (SVar 2))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_5.
Theorem native_schema_6 : forall rho, keval rho (KLet (KAdd (KVar 0) (KLit (1))) (KLet (KMul (KVar 0) (KVar 2)) (KSub (KVar 0) (KVar 1)))) = seval rho (SLet (SAdd (SVar 0) (SLit (1))) (SLet (SMul (SVar 0) (SVar 2)) (SSub (SVar 0) (SVar 1)))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_6.
Theorem native_schema_7 : forall rho, keval rho (KLet (KAdd (KVar 0) (KVar 1)) (KLet (KMul (KVar 0) (KLit (2))) (KSub (KVar 0) (KVar 3)))) = seval rho (SLet (SAdd (SVar 0) (SVar 1)) (SLet (SMul (SVar 0) (SLit (2))) (SSub (SVar 0) (SVar 3)))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_7.
Theorem native_schema_8 : forall rho, keval rho (KSub (KAdd (KVar 0) (KVar 1)) (KMul (KVar 1) (KVar 2))) = seval rho (SLet (SAdd (SVar 0) (SVar 1)) (SSub (SVar 0) (SMul (SVar 2) (SVar 3)))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_8.
Theorem native_schema_9 : forall rho, keval rho (KAdd (KVar 0) (KLit (-17))) = seval rho (SAdd (SVar 0) (SLit (-17))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_9.
Theorem native_schema_10 : forall rho, keval rho (KAdd (KVar 0) (KLit (9223372036854775808))) = seval rho (SAdd (SVar 0) (SLit (9223372036854775808))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_10.
Theorem native_schema_11 : forall rho, keval rho (KLet (KMul (KVar 0) (KVar 1)) (KAdd (KVar 1) (KVar 2))) = seval rho (SLet (SMul (SVar 0) (SVar 1)) (SAdd (SVar 1) (SVar 2))).
Proof. reflexivity. Qed.
Print Assumptions native_schema_11.
