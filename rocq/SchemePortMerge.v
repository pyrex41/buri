(* Preservation for the actual captured Shen-Scheme merge-nested-lets pass.
   Unlike the earlier two-binding instance, the tail is arbitrary syntax. *)
From Coq Require Import List String.
From Buri Require Import Native NativeComposition NativeSimulation NativeRuntime
  ObserverEffects CompilerPassInput CompilerPassCorrect.
Import ListNotations.
Module SchemePortMerge.
Import Native.Native NativeComposition.NativeComposition
  CompilerPassCorrect.CompilerPassCorrect.
Open Scope string_scope.

(* Prepending a binding to ANY successfully admitted let* tail. No freshness
   premise: let* is sequential and repeated names deliberately shadow. *)
Lemma decode_prepend : forall n x av bindings term,
 decode (S n) (let_many (Pair (L [Symbol x;av]) bindings) term) =
 match decode (S n) (let_many bindings term) with
 | Some b => match decode n av with Some a => Some (Let x a b) | _ => None end
 | _ => None end.
Proof.
 intros n x av bindings term. cbn [let_many decode L elements fold_right].
 destruct (elements bindings); destruct (decode n term); reflexivity.
Qed.

Theorem arbitrary_tail_decodes : forall n x av bindings term a b,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode (S n) (let_many bindings term) = Some b ->
 decode (S (S n)) (let_one (L [Symbol x;av]) (let_many bindings term)) =
 Some (Let x a b) /\
 decode (S n) (let_many (Pair (L [Symbol x;av]) bindings) term) =
 Some (Let x a b).
Proof.
 intros n x av bindings term a b A A' B.
 rewrite decode_one, decode_prepend, A, A', B. split; reflexivity.
Qed.

(* Includes every result: successful return, raised exception, unsupported
   operation, and exhausted fuel. Equal decoded terms use equal evaluator fuel;
   syntax decoding budgets differ because the source has an extra wrapper. *)
Theorem arbitrary_tail_preserves : forall n x av bindings term a b p rho fuel,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode (S n) (let_many bindings term) = Some b ->
 (match decode (S (S n)) (let_one (L [Symbol x;av]) (let_many bindings term)) with
  | Some e => eval fuel p rho e | _ => Unsupported end) =
 (match decode (S n) (let_many (Pair (L [Symbol x;av]) bindings) term) with
  | Some e => eval fuel p rho e | _ => Unsupported end).
Proof.
 intros. destruct (arbitrary_tail_decodes n x av bindings term a b H H0 H1) as [A B].
 rewrite A, B. reflexivity.
Qed.

Theorem arbitrary_tail_preserves_effects :
 forall n x av bindings term a b p compiler activate rho fuel previous,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode (S n) (let_many bindings term) = Some b ->
 (match decode (S (S n)) (let_one (L [Symbol x;av]) (let_many bindings term)) with
  | Some e => ObserverEffects.eval fuel p compiler activate rho e previous
  | _ => ObserverEffects.Out Unsupported previous [] end) =
 (match decode (S n) (let_many (Pair (L [Symbol x;av]) bindings) term) with
  | Some e => ObserverEffects.eval fuel p compiler activate rho e previous
  | _ => ObserverEffects.Out Unsupported previous [] end).
Proof.
 intros. destruct (arbitrary_tail_decodes n x av bindings term a b H H0 H1) as [A B].
 rewrite A, B. reflexivity.
Qed.

(* One theorem connects actual captured compiler execution to both decodings.
   The pass is executed by the existing native small-step machine, not a new
   reference rewrite function. The capture identity is compiler_pass_exact. *)
Theorem captured_arbitrary_tail_preservation :
 forall n x av bindings term a b,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode (S n) (let_many bindings term) = Some b ->
 exists target steps,
 NativeRuntime.invoke steps compiler_pass_program "kl:_scm.merge-nested-lets"
  [let_one (L [Symbol x;av]) (let_many bindings term)] = Returned target /\
 decode (S (S n)) (let_one (L [Symbol x;av]) (let_many bindings term)) =
  Some (Let x a b) /\
 decode (S n) target = Some (Let x a b).
Proof.
 intros n x av bindings term a b A A' B.
 destruct (runs_run _ _ _ _ (captured_merge_many (L [Symbol x;av]) bindings term)) as [k K].
 destruct (NativeSimulation.run_invoke _ _ _ _ _ K) as [steps S].
 exists (let_many (Pair (L [Symbol x;av]) bindings) term), steps.
 split; [exact S|]. eapply arbitrary_tail_decodes; eauto.
Qed.
End SchemePortMerge.
