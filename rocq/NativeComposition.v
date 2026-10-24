(* Compositional successful execution for the actual Native evaluator. *)
From Coq Require Import List String Arith Lia.
From Buri Require Import Native NativeSimulation.
Import ListNotations.
Module NativeComposition.
Import Native.Native NativeSimulation.NativeSimulation.
Lemma many_no_failure_return : forall n p rho es v,
 many n p rho es <> ArgumentFailure (Returned v).
Proof. exact many_no_returned_failure. Qed.
Theorem eval_monotone : forall n p rho e v,
 eval n p rho e = Returned v -> forall m, n <= m -> eval m p rho e = Returned v.
Proof.
 induction n as [|n IH]; intros p rho e v H [|m] LE; try discriminate; try lia.
 assert (M : forall es vs, many n p rho es = Values vs -> many m p rho es = Values vs).
 { induction es as [|a es IHas]; intros vs E; cbn [many] in *; [exact E|].
   destruct (eval n p rho a) eqn:A; try discriminate.
   rewrite (IH _ _ _ _ A m) by lia.
   destruct (many n p rho es) eqn:B; try discriminate.
   rewrite (IHas _ eq_refl); exact E. }
 destruct e; cbn [eval] in H |- *; try assumption.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   rewrite (IH _ _ _ _ E m) by lia.
   destruct v0; try (eapply IH; eauto; lia). destruct b; eapply IH; eauto; lia.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   rewrite (IH _ _ _ _ E m) by lia. eapply IH; eauto; lia.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   rewrite (IH _ _ _ _ E m) by lia.
   destruct v0; try (eapply IH; eauto; lia). destruct b; [eapply IH; eauto; lia|exact H].
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   rewrite (IH _ _ _ _ E m) by lia.
   destruct v0; try exact H. destruct b; [exact H|eapply IH; eauto; lia].
 - fold (many n p rho args) in H. fold (many m p rho args).
   destruct (many n p rho args) eqn:E.
   + rewrite (M _ _ E). destruct (p s); [|exact H].
     destruct (Nat.eqb _ _); try discriminate. eapply IH; eauto; lia.
   + destruct r; try discriminate. exfalso; eapply many_no_failure_return; exact E.
Qed.
Definition executes p rho e v := exists n, eval n p rho e = Returned v.
Definition runs p name vs v := exists d,
 p name = Some d /\ List.length (params d) = List.length vs /\
 executes p (arguments (params d) vs) (body d) v.
Lemma literal : forall p rho v, executes p rho (Lit v) v.
Proof. intros; exists 1; reflexivity. Qed.
Lemma variable : forall p rho s v, rho s = Some v -> executes p rho (Var s) v.
Proof. intros; exists 1; cbn [eval]; rewrite H; reflexivity. Qed.
Lemma branch : forall p rho c a b flag v,
 executes p rho c (Boolean flag) -> executes p rho (if flag then a else b) v ->
 executes p rho (If c a b) v.
Proof.
 intros p rho c a b flag v [n N] [m M]; exists (S (n+m)). cbn [eval].
 rewrite (eval_monotone _ _ _ _ _ N (n+m)) by lia.
 destruct flag; eapply eval_monotone; eauto; lia.
Qed.
Lemma binding : forall p rho s a b x v,
 executes p rho a x -> executes p (bind rho s x) b v -> executes p rho (Let s a b) v.
Proof.
 intros p rho s a b x v [n N] [m M]; exists (S (n+m)); cbn [eval].
 rewrite (eval_monotone _ _ _ _ _ N (n+m)) by lia. eapply eval_monotone; eauto; lia.
Qed.
Lemma conjunction : forall p rho a b flag v,
 executes p rho a (Boolean flag) ->
 (if flag then executes p rho b v else v = Boolean false) -> executes p rho (And a b) v.
Proof.
 intros p rho a b [] v [n N] B.
 - destruct B as [m M]; exists (S (n+m)); cbn [eval].
   rewrite (eval_monotone _ _ _ _ _ N (n+m)) by lia. eapply eval_monotone; eauto; lia.
 - subst; exists (S n); cbn [eval]; rewrite N; reflexivity.
Qed.
Lemma many_monotone : forall n p rho es vs,
 many n p rho es = Values vs -> forall m, n <= m -> many m p rho es = Values vs.
Proof.
 intros n p rho es; induction es as [|a es IH]; intros vs H m LE; cbn [many] in *; [exact H|].
 destruct (eval n p rho a) eqn:A; try discriminate.
 rewrite (eval_monotone _ _ _ _ _ A m LE).
 destruct (many n p rho es) eqn:E; try discriminate.
 rewrite (IH _ eq_refl m LE); exact H.
Qed.
Lemma arguments_execute : forall p rho es vs,
 Forall2 (executes p rho) es vs -> exists n, many n p rho es = Values vs.
Proof.
 intros p rho es vs H; induction H.
 - exists 0; reflexivity.
 - destruct H as [n N]; destruct IHForall2 as [m M]. exists (n+m); cbn [many].
   rewrite (eval_monotone _ _ _ _ _ N (n+m)) by lia.
   rewrite (many_monotone _ _ _ _ _ M (n+m)) by lia; reflexivity.
Qed.
Lemma call : forall p rho name es vs v,
 Forall2 (executes p rho) es vs -> runs p name vs v -> executes p rho (Call name es) v.
Proof.
 intros p rho name es vs v A [d [D [L [n N]]]].
 destruct (arguments_execute _ _ _ _ A) as [m M]. exists (S (n+m)); cbn [eval].
 fold (many (n+m) p rho es). rewrite (many_monotone _ _ _ _ _ M (n+m)) by lia.
 rewrite D,L,Nat.eqb_refl. eapply eval_monotone; eauto; lia.
Qed.
Lemma primitive_call : forall p rho name es vs v,
 Forall2 (executes p rho) es vs -> p name = None -> external name vs = Returned v ->
 executes p rho (Call name es) v.
Proof.
 intros p rho name es vs v A D E.
 destruct (arguments_execute _ _ _ _ A) as [n N]. exists (S n); cbn [eval].
 fold (many n p rho es); rewrite N,D; exact E.
Qed.
Theorem runs_run : forall ds name vs v,
 runs (lookup ds) name vs v -> exists n, run n ds name vs = Returned v.
Proof.
 intros ds name vs v [d [D [L [n N]]]]; exists n.
 unfold run; rewrite D,L,Nat.eqb_refl; exact N.
Qed.
End NativeComposition.
