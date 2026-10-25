(* Generic preservation for a real upstream Shen-Scheme compiler pass.
   The extracted pass body is captured after actual Shen compilation. *)
From Coq Require Import List String.
From Buri Require Import Native NativeComposition NativeSimulation NativeRuntime ObserverEffects CompilerPassInput.
Import ListNotations.
Module CompilerPassCorrect.
Import Native.Native NativeComposition.NativeComposition.
Open Scope string_scope.
Definition P := lookup compiler_pass_program.
Definition let_one binding body := L [Symbol "let";L [binding];body].
Definition let_many bindings body := L [Symbol "let*";bindings;body].
Ltac start := unfold runs; eexists; split; [reflexivity|]; split; [reflexivity|].
Theorem captured_merge_many : forall binding bindings body,
 runs P "kl:_scm.merge-nested-lets" [let_one binding (let_many bindings body)]
 (let_many (Pair binding bindings) body).
Proof. intros; start; exists 50; reflexivity. Qed.
Theorem captured_merge_two : forall a b body,
 runs P "kl:_scm.merge-nested-lets" [let_one a (let_one b body)]
 (let_many (L [a;b]) body).
Proof. intros; start; exists 50; reflexivity. Qed.
Theorem captured_merge_two_machine : forall a b body, exists steps,
 NativeRuntime.invoke steps compiler_pass_program "kl:_scm.merge-nested-lets"
 [let_one a (let_one b body)] = Returned (let_many (L [a;b]) body).
Proof.
 intros a b body; destruct (runs_run _ _ _ _ (captured_merge_two a b body)) as [n H].
 eapply NativeSimulation.run_invoke; exact H.
Qed.
Lemma decode_one : forall n x a b,
 decode (S n) (let_one (L [Symbol x;a]) b) =
 match decode n b with Some b => match decode n a with Some a=>Some (Let x a b)|_=>None end|_=>None end.
Proof. reflexivity. Qed.
Lemma decode_two : forall n x y a b c,
 decode (S n) (let_many (L [L [Symbol x;a];L [Symbol y;b]]) c) =
 match decode n c with Some c => match decode n b with Some b =>
 match decode n a with Some a => Some (Let x a (Let y b c)) | _=>None end|_=>None end|_=>None end.
Proof.
 intros; cbn [let_many decode elements L fold_right].
 destruct (decode n c), (decode n b), (decode n a); reflexivity.
Qed.
(* Subexpressions must be decoded successfully at the two enclosing depths.
   This is an explicit syntax-admission condition, not a compiler oracle. *)
Theorem merge_two_decodes : forall n x y av bv cv a b c,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode n bv = Some b -> decode n cv = Some c ->
 decode (S (S n)) (let_one (L [Symbol x;av]) (let_one (L [Symbol y;bv]) cv)) =
 Some (Let x a (Let y b c)) /\
 decode (S n) (let_many (L [L [Symbol x;av];L [Symbol y;bv]]) cv) =
 Some (Let x a (Let y b c)).
Proof.
 intros n x y av bv cv a b c A A' B C. rewrite decode_one,decode_one,decode_two; rewrite A,A',B,C; split; reflexivity.
Qed.
Theorem merge_two_preserves : forall n x y av bv cv a b c p rho fuel,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode n bv = Some b -> decode n cv = Some c ->
 (match decode (S (S n)) (let_one (L [Symbol x;av]) (let_one (L [Symbol y;bv]) cv)) with
 | Some e => eval fuel p rho e | None => Unsupported end) =
 (match decode (S n) (let_many (L [L [Symbol x;av];L [Symbol y;bv]]) cv) with
 | Some e => eval fuel p rho e | None => Unsupported end).
Proof.
 intros; destruct (merge_two_decodes n x y av bv cv a b c H H0 H1 H2) as [A B].
 rewrite A,B; reflexivity.
Qed.
Theorem merge_two_preserves_effects : forall n x y av bv cv a b c p compiler activate rho fuel previous,
 decode (S n) av = Some a -> decode n av = Some a ->
 decode n bv = Some b -> decode n cv = Some c ->
 (match decode (S (S n)) (let_one (L [Symbol x;av]) (let_one (L [Symbol y;bv]) cv)) with
 | Some e => ObserverEffects.eval fuel p compiler activate rho e previous
 | None => ObserverEffects.Out Unsupported previous [] end) =
 (match decode (S n) (let_many (L [L [Symbol x;av];L [Symbol y;bv]]) cv) with
 | Some e => ObserverEffects.eval fuel p compiler activate rho e previous
 | None => ObserverEffects.Out Unsupported previous [] end).
Proof.
 intros; destruct (merge_two_decodes n x y av bv cv a b c H H0 H1 H2) as [A B].
 rewrite A,B; reflexivity.
Qed.
End CompilerPassCorrect.
