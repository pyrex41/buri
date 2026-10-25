(* Fresh administrative let insertion for arbitrary operands and arbitrary
   remaining argument lists, including every modeled state and failure trace. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract CheckedFileIO.
Import ListNotations.
Module CallRefinement.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract.
Open Scope list_scope.
Definition fresh name args := forall e, In e args -> ~ In name (variables e).
Lemma bind_return : forall v k st, bind (ret v) k st=k v st.
Proof. intros; unfold bind,ret,return_result; cbn [answer records trace]; destruct (k v st); reflexivity. Qed.
Lemma lifted_tail : forall n p op rho name v f args st,
 fresh name args ->
 eval_with (S (S n)) p op (Native.bind rho name v) (Call f (Var name::args)) st =
 many (S n) p op rho args (fun vs=>apply (S n) p op f (v::vs)) st.
Proof.
 intros n p op rho name v f args st F. rewrite call_step. cbn [many].
 transitivity (bind (ret v) (fun x=>many (S n) p op (Native.bind rho name v) args
 (fun vs=>apply (S n) p op f (x::vs))) st).
 - apply bind_congruent; [|reflexivity]. intro state.
   cbn [eval_with]; unfold Native.bind; rewrite String.eqb_refl; reflexivity.
 - rewrite bind_return; apply many_congruent; intros e E state.
   apply fresh_binding_preserves_effects; apply F; exact E.
Qed.
Lemma apply_approximates : forall n m p op name vs,
 n<=m -> approximates (apply n p op name vs) (apply m p op name vs).
Proof.
 intros; unfold apply; destruct (p name); [destruct (Nat.eqb _ _)|]; try apply approximates_refl.
 intros st out E C; eapply eval_completed_monotone; eauto.
Qed.
Lemma tail_approximates : forall n m p op rho f args v,
 n<=m -> approximates
 (many n p op rho args (fun vs=>apply n p op f (v::vs)))
 (many m p op rho args (fun vs=>apply m p op f (v::vs))).
Proof.
 intros; apply many_approximates.
 - intros e st out E C; eapply eval_completed_monotone; eauto.
 - intro vs; apply apply_approximates; assumption.
Qed.
Theorem lift_argument_forward : forall n p op rho name f a args,
 fresh name args -> approximates
 (eval_with (S (S n)) p op rho (Call f (a::args)))
 (eval_with (S (S (S n))) p op rho (Let name a (Call f (Var name::args)))).
Proof.
 intros n p op rho name f a args F st out E C.
 rewrite call_step in E. cbn [many] in E.
 rewrite CheckedFileIO.let_step.
 assert (approximates (eval_with (S n) p op rho a) (eval_with (S (S n)) p op rho a)) as A.
 { intros state o H N; eapply eval_completed_monotone; eauto; lia. }
 assert (K:forall v, approximates
 (many (S n) p op rho args (fun vs=>apply (S n) p op f (v::vs)))
 (eval_with (S (S n)) p op (Native.bind rho name v) (Call f (Var name::args)))).
 { intros v state o H N; rewrite lifted_tail by exact F; exact H. }
 exact (bind_approximates _ _ _ _ A K st out E C).
Qed.
Theorem lift_argument_backward : forall n p op rho name f a args,
 fresh name args -> approximates
 (eval_with (S (S (S n))) p op rho (Let name a (Call f (Var name::args))))
 (eval_with (S (S (S n))) p op rho (Call f (a::args))).
Proof.
 intros n p op rho name f a args F st out E C.
 rewrite CheckedFileIO.let_step in E. rewrite call_step. cbn [many].
 assert (K:forall v, approximates
 (eval_with (S (S n)) p op (Native.bind rho name v) (Call f (Var name::args)))
 (many (S (S n)) p op rho args (fun vs=>apply (S (S n)) p op f (v::vs)))).
 { intros v state o H N; rewrite lifted_tail in H by exact F.
   exact (tail_approximates (S n) (S (S n)) p op rho f args v (Nat.le_succ_diag_r _) state o H N). }
 exact (bind_approximates _ _ _ _ (approximates_refl _) K st out E C).
Qed.
Definition observes p op rho e st out := completed out /\ exists n, eval_with n p op rho e st=out.
Theorem fresh_let_observational_equivalence : forall p op rho name f a args st out,
 fresh name args ->
 (observes p op rho (Call f (a::args)) st out <->
 observes p op rho (Let name a (Call f (Var name::args))) st out).
Proof.
 intros p op rho name f a args st out F; split; intros [C [n E]]; split; [exact C| |exact C|].
 - exists (S (S (S n))). eapply lift_argument_forward; [exact F| |exact C].
   eapply eval_completed_monotone; [exact E|exact C|lia].
 - exists (S (S (S n))). eapply lift_argument_backward; [exact F| |exact C].
   eapply eval_completed_monotone; [exact E|exact C|lia].
Qed.
Definition never_completes p op rho e st := forall out, ~ observes p op rho e st out.
Theorem fresh_let_noncompletion_equivalence : forall p op rho name f a args st,
 fresh name args ->
 (never_completes p op rho (Call f (a::args)) st <->
 never_completes p op rho (Let name a (Call f (Var name::args))) st).
Proof.
 intros; unfold never_completes; split; intros D out E; apply (D out);
 apply (fresh_let_observational_equivalence p op rho name f a args st out H); exact E.
Qed.
End CallRefinement.
