(* Full binding-list preservation for the captured upstream merge pass.
   Syntax admission is explicit and reusable at every sufficient reader depth. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native NativeComposition NativeRuntime NativeSimulation ObserverEffects CompilerPassCorrect.
Import ListNotations.
Module CompilerBindings.
Import Native.Native CompilerPassCorrect.CompilerPassCorrect.
Open Scope string_scope.
Definition stable bound syntax expression := forall fuel, bound <= fuel -> decode fuel syntax = Some expression.
Definition binding_represents bound binding named := exists syntax,
 binding = L [Symbol (fst named);syntax] /\ stable bound syntax (snd named).
Definition nest bindings body := fold_right (fun binding b => Let (fst binding) (snd binding) b) body bindings.
Fixpoint chain reader bindings body := match bindings with
 | [] => Some body
 | binding::rest => match elements binding,chain reader rest body with
   | Some [Symbol name;syntax],Some b => match reader syntax with Some a=>Some (Let name a b)|_=>None end
   | _,_=>None end end.
Lemma decode_sequence : forall fuel bindings body,
 decode (S fuel) (let_many (L bindings) body) =
 match decode fuel body with Some b => chain (decode fuel) bindings b | _=>None end.
Proof.
 intros fuel bindings body; unfold let_many. cbn [decode elements L fold_right].
 fold (L bindings). rewrite ObserverEffects.elements_list.
 destruct (decode fuel body) as [b|]; [|reflexivity].
 induction bindings as [|binding rest IH]; [reflexivity|].
 cbn [chain]. destruct (elements binding) as [xs|]; [|reflexivity].
 destruct xs as [|x [|a [|extra tail]]]; try reflexivity.
 destruct x; try reflexivity. rewrite IH; reflexivity.
Qed.
Lemma chain_correct : forall bound bindings parsed,
 Forall2 (binding_represents bound) bindings parsed -> forall fuel body,
 bound <= fuel -> chain (decode fuel) bindings body = Some (nest parsed body).
Proof.
 intros bound bindings parsed H; induction H; intros fuel b F; [reflexivity|].
 destruct y as [name expression]; destruct H as [syntax [X R]]; subst x.
 cbn [chain L fold_right elements nest fst snd]. rewrite IHForall2 by exact F.
 rewrite R by exact F; reflexivity.
Qed.
Theorem literal_stable : forall v, stable 1 (L [Symbol "quote";v]) (Lit v).
Proof. intros v [|n] H; [lia|reflexivity]. Qed.
Theorem variable_stable : forall name, stable 1 (Symbol name) (Var name).
Proof. intros name [|n] H; [lia|reflexivity]. Qed.
Theorem if_stable : forall bound c a b ce ae be,
 stable bound c ce -> stable bound a ae -> stable bound b be ->
 stable (S bound) (L [Symbol "if";c;a;b]) (If ce ae be).
Proof.
 intros bound c a b ce ae be C A B [|n] H; [lia|].
 change (match decode n c,decode n a,decode n b with
 | Some c,Some a,Some b=>Some (If c a b)|_,_,_=>None end = Some (If ce ae be)).
 rewrite C,A,B by lia; reflexivity.
Qed.
Theorem let_stable : forall bound name a b ae be,
 stable bound a ae -> stable bound b be ->
 stable (S bound) (let_one (L [Symbol name;a]) b) (Let name ae be).
Proof.
 intros bound name a b ae be A B [|n] H; [lia|].
 rewrite decode_one,A,B by lia; reflexivity.
Qed.
Theorem merge_many_decodes : forall bound fuel name syntax ae bindings parsed body be,
 stable bound syntax ae -> Forall2 (binding_represents bound) bindings parsed ->
 stable bound body be -> bound <= fuel ->
 decode (S (S fuel)) (let_one (L [Symbol name;syntax]) (let_many (L bindings) body)) =
 Some (Let name ae (nest parsed be)) /\
 decode (S fuel) (let_many (L (L [Symbol name;syntax]::bindings)) body) =
 Some (Let name ae (nest parsed be)).
Proof.
 intros bound fuel name syntax ae bindings parsed body be A BS B F.
 rewrite decode_one,decode_sequence,decode_sequence.
 rewrite B by exact F. rewrite (chain_correct bound bindings parsed BS fuel be F).
 rewrite A by lia.
 cbn [chain L fold_right elements].
 rewrite (chain_correct bound bindings parsed BS fuel be F).
 rewrite A by exact F; split; reflexivity.
Qed.
Theorem merge_many_preserves : forall bound fuel name syntax ae bindings parsed body be p rho budget,
 stable bound syntax ae -> Forall2 (binding_represents bound) bindings parsed ->
 stable bound body be -> bound <= fuel ->
 (match decode (S (S fuel)) (let_one (L [Symbol name;syntax]) (let_many (L bindings) body)) with
 | Some e=>eval budget p rho e|_=>Unsupported end) =
 (match decode (S fuel) (let_many (L (L [Symbol name;syntax]::bindings)) body) with
 | Some e=>eval budget p rho e|_=>Unsupported end).
Proof.
 intros; destruct (merge_many_decodes bound fuel name syntax ae bindings parsed body0 be H H0 H1 H2) as [A B].
 rewrite A,B; reflexivity.
Qed.
Theorem merge_many_preserves_effects : forall bound fuel name syntax ae bindings parsed body be p operation rho budget previous,
 stable bound syntax ae -> Forall2 (binding_represents bound) bindings parsed ->
 stable bound body be -> bound <= fuel ->
 (match decode (S (S fuel)) (let_one (L [Symbol name;syntax]) (let_many (L bindings) body)) with
 | Some e=>ObserverEffects.eval_with budget p operation rho e previous
 | _=>ObserverEffects.Out Unsupported previous [] end) =
 (match decode (S fuel) (let_many (L (L [Symbol name;syntax]::bindings)) body) with
 | Some e=>ObserverEffects.eval_with budget p operation rho e previous
 | _=>ObserverEffects.Out Unsupported previous [] end).
Proof.
 intros; destruct (merge_many_decodes bound fuel name syntax ae bindings parsed body0 be H H0 H1 H2) as [A B].
 rewrite A,B; reflexivity.
Qed.
Theorem captured_many_machine_preserves : forall bound fuel name syntax ae bindings parsed body be,
 stable bound syntax ae -> Forall2 (binding_represents bound) bindings parsed ->
 stable bound body be -> bound <= fuel -> exists steps,
 NativeRuntime.invoke steps CompilerPassInput.compiler_pass_program "kl:_scm.merge-nested-lets"
  [let_one (L [Symbol name;syntax]) (let_many (L bindings) body)] =
 Returned (let_many (L (L [Symbol name;syntax]::bindings)) body) /\
 forall p rho budget,
 (match decode (S (S fuel)) (let_one (L [Symbol name;syntax]) (let_many (L bindings) body)) with
 | Some e=>eval budget p rho e|_=>Unsupported end) =
 (match decode (S fuel) (let_many (L (L [Symbol name;syntax]::bindings)) body) with
 | Some e=>eval budget p rho e|_=>Unsupported end).
Proof.
 intros bound fuel name syntax ae bindings parsed body be A B C F.
 destruct (NativeComposition.runs_run _ _ _ _ (captured_merge_many (L [Symbol name;syntax]) (L bindings) body)) as [n H].
 destruct (NativeSimulation.run_invoke _ _ _ _ _ H) as [steps M].
 exists steps; split; [exact M|]. intros; eapply merge_many_preserves; eauto.
Qed.
End CompilerBindings.
