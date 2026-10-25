(* Exact success/failure summary of every stage of the actual three-form
   loader, including all frontend/backend/activation failure positions. *)
From Coq Require Import List String ZArith.
From Buri Require Import Native ObserverEffects ObserverPipeline EffectContract.
Import ListNotations.
Module ObserverTotal.
Import Native.Native ObserverEffects.ObserverEffects.
Module O := ObserverPipeline.ObserverPipeline.
Module E := EffectContract.EffectContract.
Open Scope list_scope.
Definition install_expected compiler activate name args body previous :=
 let source:=form (Symbol name) args body in
 let prefix:=[Arity (Symbol name) (Integer (Z.of_nat (List.length args)));Compile source (compiler source)] in
 match compiler source with
 | Returned target=>match activate target with
   | Returned v=>Out (Returned (Symbol name)) (O.publish name args body target previous)
     (prefix++[Activate target (Returned v);ReadRecords;WriteRecords (O.publish name args body target previous)])
   | failure=>Out failure previous (prefix++[Activate target failure]) end
 | failure=>Out failure previous prefix end.
Lemma install_activation_failure : forall n frontend compiler activate name args body target failure previous,
 compiler (form (Symbol name) args body)=Returned target -> activate target=failure -> failed failure ->
 eval_with (30+n) O.P (O.operation frontend compiler activate)
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match O.P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous =
 Out failure previous [Arity (Symbol name) (Integer (Z.of_nat (List.length args)));
 Compile (form (Symbol name) args body) (Returned target);Activate target failure].
Proof.
 intros n frontend compiler activate name args body target failure previous C A F.
 pose proof (elements_list args) as LEN. vm_compute in LEN,C,A.
 vm_compute. rewrite LEN,C,A. destruct failure; try contradiction; reflexivity.
Qed.
Theorem installer_all_outcomes : forall n frontend compiler activate name args body previous,
 eval_with (30+n) O.P (O.operation frontend compiler activate)
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match O.P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous =
 install_expected compiler activate name args body previous.
Proof.
 intros n frontend compiler activate name args body previous.
 unfold install_expected. destruct (compiler (form (Symbol name) args body)) eqn:C.
 - destruct (activate v) eqn:A.
   + rewrite O.install_success with (target:=v) (result:=v0) by assumption; reflexivity.
   + rewrite install_activation_failure with (target:=v) (failure:=Raised owner message) by (assumption||exact I); reflexivity.
   + rewrite install_activation_failure with (target:=v) (failure:=Exhausted) by (assumption||exact I); reflexivity.
   + rewrite install_activation_failure with (target:=v) (failure:=Unsupported) by (assumption||exact I); reflexivity.
 - rewrite O.install_compile_failure with (failure:=Raised owner message) by (assumption||exact I); reflexivity.
 - rewrite O.install_compile_failure with (failure:=Exhausted) by (assumption||exact I); reflexivity.
 - rewrite O.install_compile_failure with (failure:=Unsupported) by (assumption||exact I); reflexivity.
Qed.
Definition admitted_translation r name args body := match r with
 | Returned v=>v=form (Symbol name) args body | _=>True end.
Definition stage_expected frontend compiler activate source name args body previous :=
 match frontend source with
 | Returned v=>O.prepend [Frontend source (Returned v)] (install_expected compiler activate name args body previous)
 | failure=>Out failure previous [Frontend source failure] end.
Theorem stage_all_outcomes : forall frontend compiler activate a b c k source name args body previous,
 nth_error [a;b;c] k=Some source -> admitted_translation (frontend source) name args body ->
 eval_with 34 O.P (O.operation frontend compiler activate) (O.forms_rho a b c) (O.stage (S k)) previous =
 stage_expected frontend compiler activate source name args body previous.
Proof.
 intros frontend compiler activate a b c k source name args body previous K A.
 unfold O.stage; rewrite O.unary_call_step; unfold bind at 1.
 rewrite O.frontend_stage with (source:=source) by exact K.
 unfold stage_expected; destruct (frontend source) eqn:F; try reflexivity.
 cbn [admitted_translation] in A; subst v. cbn [answer records trace].
 match goal with |- _ = ?rhs => change (let next:=eval_with (30+3) O.P (O.operation frontend compiler activate)
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match O.P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous in
 Out (answer next) (records next) (Frontend source (Returned (form (Symbol name) args body))::trace next) = rhs) end.
 rewrite installer_all_outcomes.
 destruct (install_expected compiler activate name args body previous); reflexivity.
Qed.
Definition expected_three frontend compiler activate a b c name1 args1 body1 name2 args2 body2 name3 args3 body3 :=
 bind (stage_expected frontend compiler activate a name1 args1 body1) (fun _=>
 bind (stage_expected frontend compiler activate b name2 args2 body2) (fun _=>
 bind (stage_expected frontend compiler activate c name3 args3 body3) ret)).
Theorem captured_loader_all_outcomes : forall frontend compiler activate a b c
 name1 args1 body1 name2 args2 body2 name3 args3 body3 previous,
 admitted_translation (frontend a) name1 args1 body1 ->
 admitted_translation (frontend b) name2 args2 body2 ->
 admitted_translation (frontend c) name3 args3 body3 ->
 O.invoke 36 frontend compiler activate (O.input a b c) previous =
 expected_three frontend compiler activate a b c name1 args1 body1 name2 args2 body2 name3 args3 body3 previous.
Proof.
 intros frontend compiler activate a b c name1 args1 body1 name2 args2 body2 name3 args3 body3 previous A B C.
 rewrite O.loader_step,O.begin_three. unfold expected_three.
 apply E.bind_congruent.
 - intro st; eapply stage_all_outcomes with (k:=0) (source:=a); eauto.
 - intros v1 st; apply E.bind_congruent.
   + intro state; eapply stage_all_outcomes with (k:=1) (source:=b); eauto.
   + intros v2 state; apply E.bind_congruent.
     * intro current; eapply stage_all_outcomes with (k:=2) (source:=c); eauto.
     * intros v3 current; reflexivity.
Qed.
End ObserverTotal.
