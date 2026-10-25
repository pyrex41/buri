(* Actual captured fresh-name loop with arbitrary changing/erroring stateful
   generators. Only a zero occurrence count permits a successful return. *)
From Coq Require Import List String ZArith Bool Arith Lia.
From Buri Require Import Native ObserverEffects OrderCallCorrect CheckedFileIO ObserverPipeline EffectContract.
Import ListNotations.
Module FreshSupply.
Import Native.Native ObserverEffects.ObserverEffects.
Module O := OrderCallCorrect.OrderCallCorrect.
Open Scope string_scope.
Definition P := lookup O.program.
Definition operation (generate:computation) name args := match name,args with
 | "kl:gensym",[Symbol "arg"]=>generate
 | _,_=>O.operation "unused-generator" name args end.
Definition run fuel generate used previous := match P "kl:_scm.fresh-call-variable" with
 | Some d=>eval_with fuel P (operation generate) (arguments (params d) [used]) (body d) previous
 | None=>Out Unsupported previous [] end.
Definition rho used := arguments ["V5973"] [used].
Definition guard := Call "eqv?" [Lit (Integer 0);Call "kl:occurrences" [Var "W5974";Var "V5973"]].
Definition count_result candidate used := match candidate with
 | Symbol name=>Returned (Boolean (Z.eqb 0 (Z.of_nat (O.occurrences name used))))
 | _=>Unsupported end.
Lemma generate_stage : forall n generate used previous,
 eval_with (S (S n)) P (operation generate) (rho used) (Call "kl:gensym" [Lit (Symbol "arg")]) previous=generate previous.
Proof.
 intros. change (let o:=generate previous in Out (answer o) (records o) (trace o)=generate previous).
 destruct (generate previous); reflexivity.
Qed.
Lemma guard_stage : forall n generate used candidate previous,
 eval_with (S (S (S n))) P (operation generate) (Native.bind (rho used) "W5974" candidate) guard previous=
 Out (count_result candidate used) previous [].
Proof. intros; destruct candidate; reflexivity. Qed.
Lemma recurse_stage : forall n generate used candidate previous,
 eval_with (S (S (S n))) P (operation generate) (Native.bind (rho used) "W5974" candidate)
 (Call "kl:_scm.fresh-call-variable" [Var "V5973"]) previous=run (S (S n)) generate used previous.
Proof.
 intros. change (let o:=run (S (S n)) generate used previous in
 Out (answer o) (records o) (trace o)=run (S (S n)) generate used previous).
 destruct (run (S (S n)) generate used previous);reflexivity.
Qed.
Definition expected_iteration fuel generate used previous :=
 match generate previous with
 | Out (Returned (Symbol name)) updated events=>
   if Z.eqb 0 (Z.of_nat (O.occurrences name used)) then Out (Returned (Symbol name)) updated events
   else ObserverPipeline.prepend events (run fuel generate used updated)
 | Out (Returned _) updated events=>Out Unsupported updated events
 | o=>o end.
Theorem captured_iteration : forall n generate used previous,
 run (S (S (S (S (S n))))) generate used previous = expected_iteration (S (S n)) generate used previous.
Proof.
 intros n generate used previous.
 match goal with |- _ = ?rhs => change (eval_with (S (S (S (S (S n))))) P (operation generate) (rho used)
 (Let "W5974" (Call "kl:gensym" [Lit (Symbol "arg")])
 (If guard (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"]))) previous=rhs) end.
 rewrite CheckedFileIO.let_step,generate_stage.
 unfold expected_iteration. destruct (generate previous) as [r st events].
 destruct r; cbn [answer records trace]; try reflexivity.
 rewrite CheckedFileIO.if_step,guard_stage.
 destruct v; cbn [count_result answer records trace]; try (rewrite app_nil_r;reflexivity).
 destruct (Z.eqb 0 (Z.of_nat (O.occurrences s used))) eqn:C.
 - cbn [eval_with rho arguments Native.bind ret return_result]; rewrite app_nil_r;reflexivity.
 - rewrite recurse_stage; destruct (run (S (S n)) generate used st);reflexivity.
Qed.
Theorem generator_failure_propagates : forall n generate used previous failure updated events,
 generate previous=Out failure updated events -> failed failure ->
 run (S (S (S (S (S n))))) generate used previous=Out failure updated events.
Proof.
 intros; rewrite captured_iteration; unfold expected_iteration; rewrite H;
 destruct failure; try contradiction;reflexivity.
Qed.
Lemma low_guard : forall generate used candidate previous,
 eval_with 2 P (operation generate) (Native.bind (rho used) "W5974" candidate) guard previous=Out Exhausted previous [].
Proof. reflexivity. Qed.
Lemma budget_four_no_return : forall generate used previous candidate,
 answer (run 4 generate used previous)<>Returned candidate.
Proof.
 intros generate used previous candidate.
 change (answer (eval_with 4 P (operation generate) (rho used)
 (Let "W5974" (Call "kl:gensym" [Lit (Symbol "arg")])
 (If guard (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"]))) previous)<>Returned candidate).
 rewrite CheckedFileIO.let_step,generate_stage.
 destruct (generate previous) as [r st es]; destruct r; cbn [answer records trace]; try discriminate.
Qed.
Lemma run_monotone : forall n m generate used previous out,
 run n generate used previous=out -> answer out<>Exhausted -> n<=m -> run m generate used previous=out.
Proof.
 intros n m generate used previous out E C LE; unfold run in E |- *.
 destruct (P "kl:_scm.fresh-call-variable"); [|exact E].
 eapply EffectContract.eval_completed_monotone; eauto.
Qed.
Lemma low_budget_no_return : forall fuel generate used previous candidate,
 fuel<5 -> answer (run fuel generate used previous)<>Returned candidate.
Proof.
 intros fuel generate used previous candidate B E.
 destruct (run fuel generate used previous) as [r st es] eqn:R; cbn [answer] in E;subst r.
 pose proof (run_monotone fuel 4 generate used previous _ R ltac:(discriminate) ltac:(lia)) as F.
 apply (budget_four_no_return generate used previous candidate); rewrite F;reflexivity.
Qed.
Theorem successful_candidate_is_absent : forall fuel generate used previous candidate updated events,
 run fuel generate used previous=Out (Returned candidate) updated events ->
 exists name, candidate=Symbol name /\ O.occurrences name used=0.
Proof.
 intro fuel; induction fuel using lt_wf_ind; intros generate used previous candidate updated events E.
 destruct (Nat.lt_ge_cases fuel 5) as [B|B].
 - exfalso; apply (low_budget_no_return fuel generate used previous candidate B); rewrite E;reflexivity.
 - destruct fuel as [|[|[|[|[|n]]]]]; try lia.
   rewrite captured_iteration in E; unfold expected_iteration in E.
   destruct (generate previous) as [r st es]; destruct r; try discriminate.
   destruct v; try discriminate.
   destruct (Z.eqb 0 (Z.of_nat (O.occurrences s used))) eqn:C.
   + inversion E;subst; exists s;split;[reflexivity|]. apply Z.eqb_eq in C;lia.
   + unfold ObserverPipeline.prepend in E.
     destruct (run (S (S n)) generate used st) as [r st' es'] eqn:R.
     inversion E;subst; eapply (H (S (S n)));[lia|exact R].
Qed.
Definition list_generator previous := match previous with
 | Pair (Symbol name) rest=>Out (Returned (Symbol name)) rest []
 | Nil=>Out Exhausted Nil [] | _=>Out Unsupported previous [] end.
Theorem finite_supply_finds_first_absent : forall prefix selected suffix used,
 Forall (fun name=>0<O.occurrences name used) prefix -> O.occurrences selected used=0 ->
 run (5+3*List.length prefix) list_generator used (L (map Symbol (prefix++selected::suffix))) =
 Out (Returned (Symbol selected)) (L (map Symbol suffix)) [].
Proof.
 intro prefix; induction prefix as [|name prefix IH]; intros selected suffix used P A.
 - cbn [List.length Nat.mul Nat.add]. rewrite captured_iteration.
   unfold expected_iteration; cbn [list_generator L fold_right map app]. rewrite A;reflexivity.
 - inversion P as [|? ? O T];subst.
   replace (5+3*List.length (name::prefix)) with (S (S (S (S (S (3+3*List.length prefix)))))) by (cbn;lia).
   rewrite captured_iteration. unfold expected_iteration.
   cbn [map app L fold_right list_generator].
   assert (Z.eqb 0 (Z.of_nat (O.occurrences name used))=false) as C by (apply Z.eqb_neq;lia).
   rewrite C. replace (S (S (3+3*List.length prefix))) with (5+3*List.length prefix) by lia.
   rewrite IH by assumption;reflexivity.
Qed.
End FreshSupply.
