From Coq Require Import List String ZArith.
From Buri Require Import Equality Native NativeRuntime NativeReverse NativeTests ObserverEffects
 EffectContract CallRefinement PureEffectBridge StockDivisionGeneral FreshSupply EqualityAdmission EqualityCoreCorrect ObserverPipeline ObserverTotal.
Import ListNotations Native.Native.
Module StageTests.
Module E := ObserverEffects.ObserverEffects.
Module R := CallRefinement.CallRefinement.
Module Q := EqualityCoreCorrect.EqualityCoreCorrect.
Module A := EqualityAdmission.EqualityAdmission.
Open Scope string_scope.
Definition empty : env := fun _=>None.
Definition no_code : program := fun _=>None.
Definition source := Call "+" [Lit (Integer 1);Lit (Integer 2)].
Definition target := Let "tmp" (Lit (Integer 1)) (Call "+" [Var "tmp";Lit (Integer 2)]).
Example source_budget_two : E.answer (E.eval_with 2 no_code PureEffectBridge.operation empty source Nil)=Returned (Integer 3).
Proof. reflexivity. Qed.
Example target_budget_two_exhausts : E.answer (E.eval_with 2 no_code PureEffectBridge.operation empty target Nil)=Exhausted.
Proof. reflexivity. Qed.
Example target_budget_three : E.answer (E.eval_with 3 no_code PureEffectBridge.operation empty target Nil)=Returned (Integer 3).
Proof. reflexivity. Qed.
Definition capture_env := bind empty "tmp" (Integer 99).
Example unsafe_capture_changes_behavior :
 (Native.eval 6 no_code capture_env (Call "cons" [Lit (Integer 1);Var "tmp"]),
 Native.eval 6 no_code capture_env (Let "tmp" (Lit (Integer 1)) (Call "cons" [Var "tmp";Var "tmp"]))) =
 (Returned (Pair (Integer 1) (Integer 99)),Returned (Pair (Integer 1) (Integer 1))).
Proof. reflexivity. Qed.
Example fresh_premise_rejects_capture : ~R.fresh "tmp" [Var "tmp"].
Proof. intro H; apply (H (Var "tmp") (or_introl eq_refl)); left; reflexivity. Qed.
Definition loop_body := Call "loop" [].
Definition loop_program name := if String.eqb name "loop" then Some (Def [] loop_body) else None.
Example loop_evaluator_never_completes : NativeReverse.eval_diverges loop_program empty loop_body.
Proof. intro fuel; induction fuel; [reflexivity|]. cbn [Native.eval loop_body loop_program arguments]; exact IHfuel. Qed.
Example loop_machine_never_completes : NativeReverse.machine_diverges loop_program empty loop_body.
Proof. apply NativeReverse.divergence_equivalence; exact loop_evaluator_never_completes. Qed.
Example changing_generator_skips_collisions :
 FreshSupply.run 11 FreshSupply.list_generator (L [Symbol "x";Symbol "y"])
 (L [Symbol "x";Symbol "y";Symbol "z"]) = E.Out (Returned (Symbol "z")) Nil [].
Proof. vm_compute;reflexivity. Qed.
Definition failing_generator : E.computation := fun _=>E.Out (Raised (Symbol "generator") (Text "failed")) (Symbol "changed") [E.ReadRecords].
Example generator_failure_retains_effects : FreshSupply.run 5 failing_generator Nil Nil=
 E.Out (Raised (Symbol "generator") (Text "failed")) (Symbol "changed") [E.ReadRecords].
Proof. vm_compute;reflexivity. Qed.
Example generator_wrong_type_not_accepted :
 FreshSupply.run 5 (fun _=>E.Out (Returned (Integer 7)) Nil []) Nil Nil=E.Out Unsupported Nil [].
Proof. vm_compute;reflexivity. Qed.
Example negative_divisor_profile : StockDivisionGeneral.signed_ratio 5 (-2)=Some (Fraction (-5) 2).
Proof. reflexivity. Qed.
Example signed_zero_error_preserved :
 StockDivisionGeneral.invoke (StockDivisionGeneral.exact_divide (Raised (Symbol "/") (Text "zero"))) integral
 (fun _=>Unsupported) (Integer 1) (Integer 0)=E.Out (Raised (Symbol "/") (Text "zero")) Nil [].
Proof. reflexivity. Qed.
Example raw_refl_accepted : A.check_raw (Q.certificate (Refl (Equality.Var 0)))=A.AcceptedEquation (Equality.Var 0) (Equality.Var 0).
Proof. vm_compute;reflexivity. Qed.
Example raw_mismatch_invalid_derivation :
 A.check_raw (Q.certificate (Trans (Refl (Equality.Var 0)) (Refl (Equality.Var 1))))=A.InvalidDerivation.
Proof. vm_compute;reflexivity. Qed.
Example raw_negative_index_outside_profile :
 A.check_raw (L [Symbol "refl";L [Symbol "var";Integer (-1)]])=A.OutsideCertificateProfile.
Proof. vm_compute;reflexivity. Qed.
Example raw_instance_outside_profile :
 A.check_raw (Q.certificate (Instance 0 []))=A.OutsideCertificateProfile.
Proof. vm_compute;reflexivity. Qed.
Example raw_eval_payload_outside_profile :
 A.check_raw (L [Symbol "refl";L [Symbol "eval-kl";Symbol "payload"]])=A.OutsideCertificateProfile.
Proof. vm_compute;reflexivity. Qed.
Module O := ObserverPipeline.ObserverPipeline.
Definition failed := Raised (Symbol "failed") (Text "error").
Definition named_form name := E.form (Symbol name) [] Nil.
Definition failing_frontend phase failureName v := match v with
 | Symbol name=>if (Nat.eqb phase 0 && String.eqb name failureName)%bool then failed else Returned (named_form name)
 | _=>Unsupported end.
Definition failing_backend phase failureName v :=
 if (Nat.eqb phase 1 && same v (named_form failureName))%bool then failed else Returned v.
Definition failing_activation phase failureName v :=
 if (Nat.eqb phase 2 && same v (named_form failureName))%bool then failed else Returned Nil.
Definition loader phase failureName := O.invoke 36 (failing_frontend phase failureName) (failing_backend phase failureName)
 (failing_activation phase failureName) (O.input (Symbol "a") (Symbol "b") (Symbol "c")) Nil.
Definition records_count o := match elements (E.records o) with Some xs=>List.length xs|_=>99 end.
Definition failure_metrics := flat_map (fun phase=>map (fun failureName=>let o:=loader phase failureName in
 (E.answer o,List.length (E.trace o),records_count o)) ["a";"b";"c"]) [0;1;2].
Example every_loader_failure_position : failure_metrics =
 [(failed,1,0);(failed,7,1);(failed,13,2);(failed,3,0);(failed,9,1);(failed,15,2);
  (failed,4,0);(failed,10,1);(failed,16,2)].
Proof. vm_compute;reflexivity. Qed.
End StageTests.
