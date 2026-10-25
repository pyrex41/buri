(* Actual pinned call ordering helpers. Gensym is supplied by an explicit
   oracle; the captured loop still checks occurrence counts before accepting. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeHelpers OrderCallInput ObserverEffects CheckedFileIO.
Import ListNotations.
Module OrderCallCorrect.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Fixpoint occurrences name syntax : nat := match syntax with
 | Symbol s=>if String.eqb name s then 1 else 0
 | Pair a b=>occurrences name a + occurrences name b
 | _=>0 end.
Definition program := (order_call_program ++ NativeHelpers.helpers)%list.
Definition operation fresh op vs : computation := fun st=> Out
 (match op,vs with
 | "kl:gensym",[Symbol "arg"]=>Returned (Symbol fresh)
 | "kl:occurrences",[Symbol name;syntax]=>Returned (Integer (Z.of_nat (occurrences name syntax)))
 | "kl:not",[Boolean b]=>Returned (Boolean (negb b))
 | "kl:reverse",[syntax]=>match elements syntax with Some xs=>Returned (L (rev xs))|None=>Unsupported end
 | "begin",_=>Returned (last vs Nil)
 | _,_=>external op vs end) st [].
Definition invoke fuel fresh name args := match lookup program name with
 | Some d=>eval_with fuel (lookup program) (operation fresh) (arguments (params d) args) (body d) Nil
 | None=>Out Unsupported Nil [] end.
Definition fresh_rho used := arguments ["V5973"] [used].
Lemma gensym_step : forall n fresh used,
 eval_with (S (S n)) (lookup program) (operation fresh) (fresh_rho used)
 (Call "kl:gensym" [Lit (Symbol "arg")]) Nil = Out (Returned (Symbol fresh)) Nil [].
Proof. reflexivity. Qed.
Lemma occurrence_guard : forall n fresh used,
 eval_with (S (S (S n))) (lookup program) (operation fresh)
 (Native.bind (fresh_rho used) "W5974" (Symbol fresh))
 (Call "eqv?" [Lit (Integer 0);Call "kl:occurrences" [Var "W5974";Var "V5973"]]) Nil =
 Out (Returned (Boolean (Z.eqb 0 (Z.of_nat (occurrences fresh used))))) Nil [].
Proof. reflexivity. Qed.
Theorem captured_fresh_accepts_absent : forall n fresh used,
 occurrences fresh used = 0 ->
 invoke (S (S (S (S (S n))))) fresh "kl:_scm.fresh-call-variable" [used] = Out (Returned (Symbol fresh)) Nil [].
Proof.
 intros n fresh used H.
 match goal with |- _ = ?rhs => change (eval_with (S (S (S (S (S n))))) (lookup program) (operation fresh) (fresh_rho used)
 (Let "W5974" (Call "kl:gensym" [Lit (Symbol "arg")])
 (If (Call "eqv?" [Lit (Integer 0);Call "kl:occurrences" [Var "W5974";Var "V5973"]])
 (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"]))) Nil = rhs) end.
 rewrite CheckedFileIO.let_step,gensym_step. cbn [answer records trace].
 rewrite CheckedFileIO.if_step,occurrence_guard,H. reflexivity.
Qed.
Lemma collision_step : forall n fresh used,
 occurrences fresh used <> 0 ->
 invoke (S (S (S (S (S n))))) fresh "kl:_scm.fresh-call-variable" [used] =
 invoke (S (S n)) fresh "kl:_scm.fresh-call-variable" [used].
Proof.
 intros n fresh used H.
 match goal with |- _ = ?rhs => change (eval_with (S (S (S (S (S n))))) (lookup program) (operation fresh) (fresh_rho used)
 (Let "W5974" (Call "kl:gensym" [Lit (Symbol "arg")])
 (If (Call "eqv?" [Lit (Integer 0);Call "kl:occurrences" [Var "W5974";Var "V5973"]])
 (Var "W5974") (Call "kl:_scm.fresh-call-variable" [Var "V5973"]))) Nil = rhs) end.
 rewrite CheckedFileIO.let_step,gensym_step. cbn [answer records trace].
 rewrite CheckedFileIO.if_step,occurrence_guard.
 assert (Z.eqb 0 (Z.of_nat (occurrences fresh used)) = false) as E.
 { apply Z.eqb_neq; lia. }
 rewrite E. cbn [answer records trace].
 change (let next := invoke (S (S n)) fresh "kl:_scm.fresh-call-variable" [used] in
 Out (answer next) (records next) (trace next) = invoke (S (S n)) fresh "kl:_scm.fresh-call-variable" [used]).
 destruct (invoke (S (S n)) fresh "kl:_scm.fresh-call-variable" [used]); reflexivity.
Qed.
Theorem captured_collision_exhausts : forall fuel fresh used,
 occurrences fresh used <> 0 ->
 invoke fuel fresh "kl:_scm.fresh-call-variable" [used] = Out Exhausted Nil [].
Proof.
 intro fuel; induction fuel using lt_wf_ind; intros fresh used Hocc.
 destruct fuel as [|[|[|[|[|n]]]]]; try reflexivity.
 rewrite collision_step by exact Hocc.
 apply H; [lia|exact Hocc].
Qed.
Theorem occurrences_pair_absent : forall fresh a b,
 occurrences fresh (Pair a b) = 0 -> occurrences fresh a = 0 /\ occurrences fresh b = 0.
Proof. intros; cbn [occurrences] in H; lia. Qed.
Theorem fresh_is_distinct : forall fresh name,
 occurrences fresh (Symbol name) = 0 -> fresh <> name.
Proof. intros fresh name H E; subst; cbn [occurrences] in H; rewrite String.eqb_refl in H; discriminate. Qed.
Theorem two_computations_preserve_effects : forall operation rho state tmp f g h,
 eval_with 3 (fun _=>None) operation rho (Call f [Call g [];Call h []]) state =
 eval_with 4 (fun _=>None) operation rho
 (Let tmp (Call g []) (Call f [Var tmp;Call h []])) state.
Proof.
 intros operation rho state tmp f g h.
 cbn [eval_with ret return_result Native.bind].
 unfold bind,ret,return_result.
 destruct (operation g [] state) as [r s es]; cbn.
 destruct r; cbn; try reflexivity.
 unfold Native.bind. rewrite String.eqb_refl; cbn.
 destruct (operation h [] s) as [r' s' es']; cbn.
 destruct r'; cbn; try reflexivity.
Qed.
Theorem captured_quote_is_simple : forall fresh v,
 invoke 10 fresh "kl:_scm.simple-scheme-expression?" [L [Symbol "quote";v]] = Out (Returned (Boolean true)) Nil [].
Proof. reflexivity. Qed.
Theorem captured_symbol_is_simple : forall fresh name,
 invoke 10 fresh "kl:_scm.simple-scheme-expression?" [Symbol name] = Out (Returned (Boolean true)) Nil [].
Proof. reflexivity. Qed.
Definition call_input := L [Symbol "combine";L [Symbol "left"];L [Symbol "right"]].
Definition call_output := L [Symbol "let";L [L [Symbol "arg-proof";L [Symbol "left"]]];
 L [Symbol "combine";Symbol "arg-proof";L [Symbol "right"]]].
Theorem captured_two_computations :
 invoke 80 "arg-proof" "kl:_scm.order-call" [call_input] = Out (Returned call_output) Nil [].
Proof. vm_compute; reflexivity. Qed.
Theorem captured_two_computations_decode :
 decode 10 call_input = Some (Call "combine" [Call "left" [];Call "right" []]) /\
 decode 10 call_output = Some (Let "arg-proof" (Call "left" []) (Call "combine" [Var "arg-proof";Call "right" []])).
Proof. split; reflexivity. Qed.
Theorem captured_two_computations_preserve : forall operation rho state,
 (match decode 10 call_input with Some e=>eval_with 3 (fun _=>None) operation rho e state|None=>Out Unsupported state [] end) =
 (match decode 10 call_output with Some e=>eval_with 4 (fun _=>None) operation rho e state|None=>Out Unsupported state [] end).
Proof. intros; apply two_computations_preserve_effects. Qed.
Theorem captured_fresh_success_is_absent : forall fuel fresh used v,
 invoke fuel fresh "kl:_scm.fresh-call-variable" [used] = Out (Returned v) Nil [] ->
 v = Symbol fresh /\ occurrences fresh used = 0.
Proof.
 intros fuel fresh used v H.
 destruct (Nat.eq_dec (occurrences fresh used) 0) as [A|C].
 - destruct fuel as [|[|[|[|[|n]]]]]; try discriminate.
   rewrite captured_fresh_accepts_absent in H by exact A.
   inversion H; auto.
 - rewrite captured_collision_exhausts in H by exact C; discriminate.
Qed.
Theorem accepted_name_preserves_existing_bindings : forall fuel fresh used v rho bound name,
 invoke fuel fresh "kl:_scm.fresh-call-variable" [used] = Out (Returned v) Nil [] ->
 (0 < occurrences name used)%nat -> Native.bind rho fresh bound name = rho name.
Proof.
 intros fuel fresh used v rho bound name H O.
 destruct (captured_fresh_success_is_absent fuel fresh used v H) as [_ A].
 unfold Native.bind. destruct (String.eqb name fresh) eqn:E; [|reflexivity].
 apply String.eqb_eq in E; subst; lia.
Qed.
End OrderCallCorrect.
