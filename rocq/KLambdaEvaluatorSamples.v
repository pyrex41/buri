(* E2E-07 ground derivations: the actual Native evaluator running the captured
   klambda.shen program on concrete inputs (vm-checked), and the universal
   refinement theorem instantiated on them, so the premises are inhabited.
   These are ground evidence, not universal claims. *)
From Coq Require Import List String ZArith.
From Buri Require Import Observation KLSyntax KLValue KLSemantics Native KLambdaEvaluatorCapture
 KLambdaEvaluatorRefinement.
Import ListNotations.
Module KLambdaEvaluatorSamples.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Import KLambdaEvaluatorCapture.KLambdaEvaluatorCapture KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.
Open Scope string_scope.

Definition run_eval (e : term) (z : Z) :=
 Native.Native.run 400 program "kl:buri.eval" [Native.Native.Nil; enc_term e; enc_env []; Native.Native.Integer z].

(* (let x 1 (+ x 2)) *)
Definition p_let := TLet "x" (TLit (RInt 1)) (TPrim "+" [TVar "x"; TLit (RInt 2)]).
Theorem sample_let : run_eval p_let 20 = Native.Native.Returned (enc_verdict (WRet (RInt 3))).
Proof. vm_compute. reflexivity. Qed.
(* (trap (raise "boom") (lambda m m)) *)
Definition p_trap := TTrap (TRaise (TLit (RStr "boom"))) (TLambda "m" (TVar "m")).
Theorem sample_trap : run_eval p_trap 20 = Native.Native.Returned (enc_verdict (WRet (RStr "boom"))).
Proof. vm_compute. reflexivity. Qed.
(* (if 1 2 3): non-Boolean condition *)
Definition p_nonbool := TIf (TLit (RInt 1)) (TLit (RInt 2)) (TLit (RInt 3)).
Theorem sample_nonbool : run_eval p_nonbool 20 = Native.Native.Returned (enc_verdict (WRaise "nonboolean-condition")).
Proof. vm_compute. reflexivity. Qed.
(* apply (lambda f (f 4)) to (lambda y (y times y)); under budget 2 it is exhausted *)
Definition p_app := TApply (TLambda "f" (TApply (TVar "f") (TLit (RInt 4))))
 (TLambda "y" (TPrim "*" [TVar "y"; TVar "y"])).
Theorem sample_app : run_eval p_app 20 = Native.Native.Returned (enc_verdict (WRet (RInt 16))).
Proof. vm_compute. reflexivity. Qed.
Theorem sample_budget : run_eval p_app 2 = Native.Native.Returned (enc_verdict WBudget).
Proof. vm_compute. reflexivity. Qed.
(* (= (lambda x x) (lambda x x)): equality of two function values is
   undefined in the agreed profile; the evaluator answers unsupported. *)
Definition p_closure_eq := TPrim "=" [TLambda "x" (TVar "x"); TLambda "x" (TVar "x")].
Theorem sample_closure_eq : run_eval p_closure_eq 20 = Native.Native.Returned (enc_verdict WUnsupported).
Proof. vm_compute. reflexivity. Qed.
(* (= (lambda x x) 1): a function value is unequal to data, as in KLValue.kl_eq. *)
Definition p_closure_data_eq := TPrim "=" [TLambda "x" (TVar "x"); TLit (RInt 1)].
Theorem sample_closure_data_eq : run_eval p_closure_data_eq 20 = Native.Native.Returned (enc_verdict (WRet (RBool false))).
Proof. vm_compute. reflexivity. Qed.

Theorem samples_in_profile : sub p_let /\ sub p_trap /\ sub p_nonbool /\ sub p_app /\ sub p_closure_eq.
Proof. vm_compute. tauto. Qed.

(* The universal theorem applied to a ground run: the KLambda machine returns 3. *)
Theorem sample_let_machine : forall P s, pure P -> prims s ->
 exists m, krun P m (Cfg (Eval [] (tr p_let)) [] s) tt = VDone [] (Normal (VNum (NInt 3))).
Proof.
 intros P s HP Hs. destruct (klambda_refines 400 _ _ _ _ (proj1 samples_in_profile) sample_let) as (w & E & _ & G).
 assert (w = WRet (RInt 3)) as ->.
 { destruct w as [[]| | |]; vm_compute in E; try discriminate E; injection E as <-; reflexivity. }
 exact (G P s HP Hs).
Qed.
(* KLambda's own answer on the same program, by computation (independent check). *)
Theorem sample_let_kl :
 krun pure_profile 40 (Cfg (Eval [] (tr p_let)) [] prim_store) tt = VDone [] (Normal (VNum (NInt 3))).
Proof. vm_compute. reflexivity. Qed.
End KLambdaEvaluatorSamples.
