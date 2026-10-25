(* Execute the captured three-form loader, not a separately written plan. *)
From Coq Require Import List String ZArith Lia.
From Buri Require Import Native ObserverEffects ObserverFormsInput CheckedFileIO.
Import ListNotations.
Module ObserverPipeline.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Definition P := lookup observer_forms_program.
Definition operation (frontend compiler activate:value->result) name args : computation :=
 match name,args with
 | "kl:shen.shen->kl-h",[source]=>fun st=>Out (frontend source) st [Frontend source (frontend source)]
 | _,_=>dispatch compiler activate name args end.
Definition invoke fuel frontend compiler activate args previous :=
 match P "kl:buri.observe-forms" with
 | Some d=>eval_with fuel P (operation frontend compiler activate) (arguments (params d) [args]) (body d) previous
 | None=>Out Unsupported previous [] end.
Definition publish name args body target previous := Pair (L [form (Symbol name) args body;target]) previous.
Definition installed_trace name args body target result previous :=
 [Arity (Symbol name) (Integer (Z.of_nat (List.length args)));
 Compile (form (Symbol name) args body) (Returned target);Activate target (Returned result);
 ReadRecords;WriteRecords (publish name args body target previous)].
Lemma install_success : forall n frontend compiler activate name args body target result previous,
 compiler (form (Symbol name) args body) = Returned target -> activate target = Returned result ->
 eval_with (30+n) P (operation frontend compiler activate) (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous =
 Out (Returned (Symbol name)) (publish name args body target previous)
 (installed_trace name args body target result previous).
Proof.
 intros n frontend compiler activate name args body target result previous C A.
 pose proof (elements_list args) as LEN.
 vm_compute in LEN,C,A. vm_compute. rewrite LEN,C,A. reflexivity.
Qed.
Definition input a b c := L [L [Symbol "tc";Symbol "-"];a;b;c].
Definition forms_rho a b c := arguments ["V5972"] [input a b c].
Definition source_at k := (fix tail k v := match k with 0=>v|S n=>tail n (Call "cdr" [v]) end) k (Var "V5972").
Definition stage k := Call "kl:buri.install-observed" [Call "kl:shen.shen->kl-h" [Call "car" [source_at k]]].
Lemma source_read_stage : forall frontend compiler activate a b c previous,
 eval_with 32 P (operation frontend compiler activate) (forms_rho a b c)
 (Call "kl:shen.shen->kl-h" [Call "car" [source_at 1]]) previous =
 Out (frontend a) previous [Frontend a (frontend a)].
Proof. reflexivity. Qed.
Lemma unary_call_step : forall n p op rho name arg previous,
 eval_with (S n) p op rho (Call name [arg]) previous =
 bind (eval_with n p op rho arg) (fun v=>match p name with
 | Some d=>if Nat.eqb (List.length (params d)) 1 then eval_with n p op (arguments (params d) [v]) (Native.body d)
 else return_result Unsupported | None=>op name [v] end) previous.
Proof. reflexivity. Qed.
Lemma frontend_stage : forall frontend compiler activate a b c k source previous,
 nth_error [a;b;c] k = Some source ->
 eval_with 33 P (operation frontend compiler activate) (forms_rho a b c)
 (Call "kl:shen.shen->kl-h" [Call "car" [source_at (S k)]]) previous =
 Out (frontend source) previous [Frontend source (frontend source)].
Proof.
 intros frontend compiler activate a b c k source previous H.
 assert (k < 3)%nat as B.
 { apply (proj1 (nth_error_Some [a;b;c] k)); rewrite H; discriminate. }
 destruct k as [|[|[|k]]]; try lia; inversion H; subst; reflexivity.
Qed.
Lemma stage_success : forall frontend compiler activate a b c k source name args body target result previous,
 nth_error [a;b;c] k = Some source ->
 frontend source = Returned (form (Symbol name) args body) ->
 compiler (form (Symbol name) args body) = Returned target -> activate target = Returned result ->
 eval_with 34 P (operation frontend compiler activate) (forms_rho a b c) (stage (S k)) previous =
 Out (Returned (Symbol name)) (publish name args body target previous)
 (Frontend source (Returned (form (Symbol name) args body))::installed_trace name args body target result previous).
Proof.
 intros frontend compiler activate a b c k source name args body target result previous K F C A.
 unfold stage; rewrite unary_call_step.
 unfold bind at 1.
 rewrite frontend_stage with (source:=source) by exact K.
 rewrite F. cbn [answer records trace].
 match goal with |- _ = ?rhs => change (let next:=eval_with (30+3) P (operation frontend compiler activate)
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous in
 Out (answer next) (records next)
 (Frontend source (Returned (form (Symbol name) args body))::trace next) = rhs) end.
 rewrite install_success with (target:=target) (result:=result) by assumption; reflexivity.
Qed.
Definition loader_body := Eval vm_compute in
 match P "kl:buri.observe-forms" with Some d=>Native.body d|None=>Lit Nil end.
Definition loader_guard := match loader_body with If c _ _=>c|_=>Lit (Boolean false) end.
Lemma loader_shape : loader_body = If loader_guard (Call "begin" [stage 1;stage 2;stage 3])
 (Call "error" [Lit (Symbol "buri.observe-forms");Lit (Text "Observed loader requires tc- and three definitions")]).
Proof. reflexivity. Qed.
Lemma guard_true : forall frontend compiler activate a b c previous,
 eval_with 35 P (operation frontend compiler activate) (forms_rho a b c) loader_guard previous =
 Out (Returned (Boolean true)) previous [].
Proof. reflexivity. Qed.
Lemma loader_step : forall frontend compiler activate a b c previous,
 invoke 36 frontend compiler activate (input a b c) previous =
 eval_with 35 P (operation frontend compiler activate) (forms_rho a b c)
 (Call "begin" [stage 1;stage 2;stage 3]) previous.
Proof.
 intros.
 match goal with |- _ = ?rhs => change (eval_with 36 P (operation frontend compiler activate) (forms_rho a b c)
 (If loader_guard (Call "begin" [stage 1;stage 2;stage 3])
 (Call "error" [Lit (Symbol "buri.observe-forms");Lit (Text "Observed loader requires tc- and three definitions")])) previous = rhs) end.
 rewrite CheckedFileIO.if_step,guard_true. cbn [answer records trace].
 destruct (eval_with 35 P (operation frontend compiler activate) (forms_rho a b c)
 (Call "begin" [stage 1;stage 2;stage 3]) previous); reflexivity.
Qed.
Lemma begin_three : forall n frontend compiler activate rho a b c previous,
 eval_with (S n) P (operation frontend compiler activate) rho (Call "begin" [a;b;c]) previous =
 bind (eval_with n P (operation frontend compiler activate) rho a) (fun x=>
 bind (eval_with n P (operation frontend compiler activate) rho b) (fun y=>
 bind (eval_with n P (operation frontend compiler activate) rho c) (fun z=>
 operation frontend compiler activate "begin" [x;y;z]))) previous.
Proof. reflexivity. Qed.
Definition prepend events o := match o with Out r st es=>Out r st (events++es) end.
Lemma bind_success : forall m k previous v updated events,
 m previous = Out (Returned v) updated events ->
 bind m k previous = prepend events (k v updated).
Proof. intros m k previous v updated events H; unfold bind; rewrite H; cbn [answer records trace]; destruct (k v updated); reflexivity. Qed.
Theorem captured_three_installs : forall frontend compiler activate a b c
 name1 args1 body1 target1 result1 name2 args2 body2 target2 result2 name3 args3 body3 target3 result3 previous,
 frontend a = Returned (form (Symbol name1) args1 body1) ->
 compiler (form (Symbol name1) args1 body1) = Returned target1 -> activate target1 = Returned result1 ->
 frontend b = Returned (form (Symbol name2) args2 body2) ->
 compiler (form (Symbol name2) args2 body2) = Returned target2 -> activate target2 = Returned result2 ->
 frontend c = Returned (form (Symbol name3) args3 body3) ->
 compiler (form (Symbol name3) args3 body3) = Returned target3 -> activate target3 = Returned result3 ->
 let state1:=publish name1 args1 body1 target1 previous in
 let state2:=publish name2 args2 body2 target2 state1 in
 let state3:=publish name3 args3 body3 target3 state2 in
 invoke 36 frontend compiler activate (input a b c) previous =
 Out (Returned (Symbol name3)) state3
 ((Frontend a (Returned (form (Symbol name1) args1 body1))::installed_trace name1 args1 body1 target1 result1 previous) ++
 ((Frontend b (Returned (form (Symbol name2) args2 body2))::installed_trace name2 args2 body2 target2 result2 state1) ++
 (Frontend c (Returned (form (Symbol name3) args3 body3))::installed_trace name3 args3 body3 target3 result3 state2))).
Proof.
 intros frontend compiler activate a b c name1 args1 body1 target1 result1 name2 args2 body2 target2 result2
 name3 args3 body3 target3 result3 previous F1 C1 A1 F2 C2 A2 F3 C3 A3.
 cbn zeta. rewrite loader_step,begin_three.
 erewrite bind_success; [|eapply stage_success with (k:=0) (source:=a) (target:=target1) (result:=result1); eauto].
 erewrite bind_success; [|eapply stage_success with (k:=1) (source:=b) (target:=target2) (result:=result2); eauto].
 erewrite bind_success; [|eapply stage_success with (k:=2) (source:=c) (target:=target3) (result:=result3); eauto].
 reflexivity.
Qed.
Lemma stage_frontend_failure : forall frontend compiler activate a b c k source failure previous,
 nth_error [a;b;c] k = Some source -> frontend source = failure -> failed failure ->
 eval_with 34 P (operation frontend compiler activate) (forms_rho a b c) (stage (S k)) previous =
 Out failure previous [Frontend source failure].
Proof.
 intros frontend compiler activate a b c k source failure previous K F H.
 unfold stage; rewrite unary_call_step; unfold bind at 1.
 rewrite frontend_stage with (source:=source) by exact K. rewrite F.
 destruct failure; try contradiction; reflexivity.
Qed.
Lemma bind_failure : forall m k previous failure events,
 m previous = Out failure previous events -> failed failure ->
 bind m k previous = Out failure previous events.
Proof.
 intros m k previous failure events E H; unfold bind; rewrite E;
 destruct failure; try contradiction; reflexivity.
Qed.
Theorem captured_frontend_failure : forall frontend compiler activate a b c failure previous,
 frontend a = failure -> failed failure ->
 invoke 36 frontend compiler activate (input a b c) previous = Out failure previous [Frontend a failure].
Proof.
 intros frontend compiler activate a b c failure previous F H.
 rewrite loader_step,begin_three.
 eapply bind_failure; [eapply stage_frontend_failure with (k:=0) (source:=a); eauto|exact H].
Qed.
Theorem captured_second_frontend_failure : forall frontend compiler activate a b c
 name args body target result failure previous,
 frontend a = Returned (form (Symbol name) args body) ->
 compiler (form (Symbol name) args body) = Returned target -> activate target = Returned result ->
 frontend b = failure -> failed failure ->
 invoke 36 frontend compiler activate (input a b c) previous =
 Out failure (publish name args body target previous)
 ((Frontend a (Returned (form (Symbol name) args body))::installed_trace name args body target result previous) ++
 [Frontend b failure]).
Proof.
 intros frontend compiler activate a b c name args body target result failure previous F C A B H.
 rewrite loader_step,begin_three.
 erewrite bind_success; [|eapply stage_success with (k:=0) (source:=a) (target:=target) (result:=result); eauto].
 erewrite bind_failure; [reflexivity|eapply stage_frontend_failure with (k:=1) (source:=b); eauto|exact H].
Qed.
Lemma install_compile_failure : forall n frontend compiler activate name args body failure previous,
 compiler (form (Symbol name) args body) = failure -> failed failure ->
 eval_with (30+n) P (operation frontend compiler activate) (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous =
 Out failure previous [Arity (Symbol name) (Integer (Z.of_nat (List.length args)));
 Compile (form (Symbol name) args body) failure].
Proof.
 intros n frontend compiler activate name args body failure previous C F.
 pose proof (elements_list args) as LEN.
 vm_compute in LEN,C. vm_compute. rewrite LEN,C.
 destruct failure; try contradiction; reflexivity.
Qed.
Lemma stage_compile_failure : forall frontend compiler activate a b c k source name args body failure previous,
 nth_error [a;b;c] k = Some source -> frontend source = Returned (form (Symbol name) args body) ->
 compiler (form (Symbol name) args body) = failure -> failed failure ->
 eval_with 34 P (operation frontend compiler activate) (forms_rho a b c) (stage (S k)) previous =
 Out failure previous [Frontend source (Returned (form (Symbol name) args body));
 Arity (Symbol name) (Integer (Z.of_nat (List.length args)));Compile (form (Symbol name) args body) failure].
Proof.
 intros frontend compiler activate a b c k source name args body failure previous K F C H.
 unfold stage; rewrite unary_call_step; unfold bind at 1.
 rewrite frontend_stage with (source:=source) by exact K. rewrite F.
 cbn [answer records trace].
 match goal with |- _ = ?rhs => change (let next:=eval_with (30+3) P (operation frontend compiler activate)
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match P "kl:buri.install-observed" with Some d=>d|None=>Def [] (Lit Nil) end)) previous in
 Out (answer next) (records next)
 (Frontend source (Returned (form (Symbol name) args body))::trace next) = rhs) end.
 rewrite install_compile_failure with (failure:=failure) by assumption; reflexivity.
Qed.
Theorem captured_third_compile_failure : forall frontend compiler activate a b c
 name1 args1 body1 target1 result1 name2 args2 body2 target2 result2 name3 args3 body3 failure previous,
 frontend a = Returned (form (Symbol name1) args1 body1) ->
 compiler (form (Symbol name1) args1 body1) = Returned target1 -> activate target1 = Returned result1 ->
 frontend b = Returned (form (Symbol name2) args2 body2) ->
 compiler (form (Symbol name2) args2 body2) = Returned target2 -> activate target2 = Returned result2 ->
 frontend c = Returned (form (Symbol name3) args3 body3) ->
 compiler (form (Symbol name3) args3 body3) = failure -> failed failure ->
 let state1:=publish name1 args1 body1 target1 previous in
 let state2:=publish name2 args2 body2 target2 state1 in
 invoke 36 frontend compiler activate (input a b c) previous = Out failure state2
 ((Frontend a (Returned (form (Symbol name1) args1 body1))::installed_trace name1 args1 body1 target1 result1 previous) ++
 ((Frontend b (Returned (form (Symbol name2) args2 body2))::installed_trace name2 args2 body2 target2 result2 state1) ++
 [Frontend c (Returned (form (Symbol name3) args3 body3));Arity (Symbol name3) (Integer (Z.of_nat (List.length args3)));
 Compile (form (Symbol name3) args3 body3) failure])).
Proof.
 intros frontend compiler activate a b c name1 args1 body1 target1 result1 name2 args2 body2 target2 result2
 name3 args3 body3 failure previous F1 C1 A1 F2 C2 A2 F3 C3 H.
 cbn zeta. rewrite loader_step,begin_three.
 erewrite bind_success; [|eapply stage_success with (k:=0) (source:=a) (target:=target1) (result:=result1); eauto].
 erewrite bind_success; [|eapply stage_success with (k:=1) (source:=b) (target:=target2) (result:=result2); eauto].
 erewrite bind_failure; [reflexivity|eapply stage_compile_failure with (k:=2) (source:=c); eauto|exact H].
Qed.
End ObserverPipeline.
