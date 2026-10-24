(* The functional evaluator and instruction machine agree on every successful
   evaluation, for arbitrary private programs, environments and continuations.
   This is a theorem about Buri's semantics, not about the Chez compiler. *)
From Coq Require Import List String Relation_Operators.
From Buri Require Import Native NativeRuntime.
Import ListNotations.
Module NativeSimulation.
Import Native.Native NativeRuntime.NativeRuntime.
Open Scope list_scope.
Definition many fuel p rho := fix go es := match es with
 | [] => Values []
 | e::es => match eval fuel p rho e with
   | Returned v => match go es with Values vs => Values (v::vs) | ArgumentFailure r => ArgumentFailure r end
   | r => ArgumentFailure r end end.
Lemma many_no_returned_failure : forall fuel p rho es v,
 many fuel p rho es <> ArgumentFailure (Returned v).
Proof.
 intros fuel p rho es; induction es as [|e es IH]; intros v H; [discriminate|].
 cbn [many] in H. destruct (eval fuel p rho e); try discriminate.
 destruct (many fuel p rho es) eqn:E; try discriminate.
 inversion H; subst. eapply IH; reflexivity.
Qed.
Lemma chain : forall p a b c, reaches p a b -> reaches p b c -> reaches p a c.
Proof. intros p a b c H; unfold reaches in *; induction H; intros; [assumption|eapply rt1n_trans; eauto]. Qed.
Lemma one : forall p a b, step p a = Some b -> reaches p a b.
Proof. intros; eapply rt1n_trans; [exact H|constructor]. Qed.

Theorem eval_trace : forall fuel p rho e v,
 eval fuel p rho e = Returned v -> forall k,
 reaches p (Enter rho e,k) (Deliver v,k).
Proof.
 induction fuel as [|n IH]; intros p rho e v H k; [discriminate|].
 assert (ARGS : forall es vs name acc stack,
   many n p rho es = Values vs ->
   reaches p (match es with
     | [] => apply p name (rev acc) stack
     | a::rest => (Enter rho a,Arguments rho name rest acc::stack) end)
     (apply p name (rev acc ++ vs) stack)).
 { induction es as [|a es IHas]; intros vs name acc stack E.
   - cbn [many] in E; inversion E; subst. rewrite app_nil_r. constructor.
   - cbn [many] in E. destruct (eval n p rho a) eqn:A; try discriminate.
     destruct (many n p rho es) eqn:B; try discriminate. inversion E; subst.
     eapply chain; [eapply IH; exact A|].
     destruct es as [|b es].
     + cbn [many] in B; inversion B; subst. cbn.
       replace (rev acc ++ [v0]) with (rev (v0::acc)) by (cbn; reflexivity).
       apply one; reflexivity.
     + eapply chain; [apply one; reflexivity|].
       specialize (IHas _ name (v0::acc) stack eq_refl).
       cbn [rev] in IHas. rewrite <- app_assoc in IHas. exact IHas. }
 destruct e; cbn [eval] in H.
 - inversion H; subst; apply one; reflexivity.
 - destruct (rho s) eqn:E; try discriminate. inversion H; subst.
   apply one; cbn [step]; rewrite E; reflexivity.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   eapply chain; [apply one; reflexivity|].
   eapply chain; [eapply IH; exact E|].
   eapply chain; [apply one; reflexivity|].
   destruct v0; try (eapply IH; exact H).
   destruct b; eapply IH; exact H.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   eapply chain; [apply one; reflexivity|].
   eapply chain; [eapply IH; exact E|].
   eapply chain; [apply one; reflexivity|]. eapply IH; exact H.
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   eapply chain; [apply one; reflexivity|].
   eapply chain; [eapply IH; exact E|].
   eapply chain; [apply one; reflexivity|].
   destruct v0; try (eapply IH; exact H).
   destruct b; [eapply IH; exact H|inversion H; subst; constructor].
 - destruct (eval n p rho e1) eqn:E; try discriminate.
   eapply chain; [apply one; reflexivity|].
   eapply chain; [eapply IH; exact E|].
   eapply chain; [apply one; reflexivity|].
   destruct v0; try (inversion H; subst; constructor).
   destruct b; [inversion H; subst; constructor|eapply IH; exact H].
 - change (match many n p rho args with
    | Values vs => match p s with
      | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
        then eval n p (arguments (params d) vs) (body d) else Unsupported
      | None => external s vs end
    | ArgumentFailure r => r end = Returned v) in H.
   destruct (many n p rho args) eqn:E; [|destruct r; try discriminate; exfalso; eapply many_no_returned_failure; exact E].
   eapply chain with (b := match args with
    | [] => apply p s [] k
    | a::rest => (Enter rho a,Arguments rho s rest []::k) end).
   { apply one; destruct args; reflexivity. }
   eapply chain; [exact (ARGS args vs s [] k E)|]. cbn [rev app].
   unfold apply. destruct (p s) as [d|] eqn:D.
   + destruct (Nat.eqb _ _) eqn:A; try discriminate. eapply IH; exact H.
   + rewrite H. constructor.
Qed.
(* Faults retain the exact owner/message and stop argument evaluation. A
   fault may retain extra continuation frames, which execute never resumes. *)
Definition failure r := match r with Raised _ _ | Unsupported => True | _ => False end.
Lemma arguments_trace : forall fuel p rho es vs name acc stack,
 many fuel p rho es = Values vs ->
 reaches p (match es with
   | [] => apply p name (rev acc) stack
   | a::rest => (Enter rho a,Arguments rho name rest acc::stack) end)
   (apply p name (rev acc ++ vs) stack).
Proof.
 intros fuel p rho es; induction es as [|a es IH]; intros vs name acc stack E.
 - cbn [many] in E; inversion E; subst; rewrite app_nil_r; constructor.
 - cbn [many] in E. destruct (eval fuel p rho a) eqn:A; try discriminate.
   destruct (many fuel p rho es) eqn:B; try discriminate. inversion E; subst.
   eapply chain; [eapply eval_trace; exact A|].
   destruct es as [|b es].
   + cbn [many] in B; inversion B; subst. apply one; reflexivity.
   + eapply chain; [apply one; reflexivity|].
     specialize (IH _ name (v::acc) stack eq_refl).
     cbn [rev] in IH; rewrite <- app_assoc in IH; exact IH.
Qed.
Lemma arguments_failure_trace : forall fuel p rho,
 (forall e r, eval fuel p rho e = r -> failure r -> forall k,
   exists k', reaches p (Enter rho e,k) (Fault r,k')) ->
 forall es r name acc stack,
 many fuel p rho es = ArgumentFailure r -> failure r ->
 exists k', reaches p (match es with
   | [] => apply p name (rev acc) stack
   | a::rest => (Enter rho a,Arguments rho name rest acc::stack) end) (Fault r,k').
Proof.
 intros fuel p rho IH es; induction es as [|a es IHas]; intros r name acc stack E F;
   [discriminate|].
 cbn [many] in E. destruct (eval fuel p rho a) eqn:A.
 - destruct (many fuel p rho es) eqn:B; try discriminate. inversion E; subst.
   destruct es as [|b es]; [discriminate|].
   destruct (IHas r name (v::acc) stack eq_refl F) as [k' T]. exists k'.
   eapply chain; [eapply eval_trace; exact A|].
   eapply chain; [apply one; reflexivity|exact T].
 - inversion E; subst; eapply IH; eauto.
 - inversion E; subst; contradiction.
 - inversion E; subst; eapply IH; eauto.
Qed.
Theorem eval_failure_trace : forall fuel p rho e r,
 eval fuel p rho e = r -> failure r -> forall k,
 exists k', reaches p (Enter rho e,k) (Fault r,k').
Proof.
 induction fuel as [|n IH]; intros p rho e r H F k.
 { cbn [eval] in H; subst; contradiction. }
 destruct e; cbn [eval] in H.
 - subst; contradiction.
 - destruct (rho s) eqn:E; [subst; contradiction|]. subst.
   exists k; apply one; cbn [step]; rewrite E; reflexivity.
 - destruct (eval n p rho e1) eqn:E.
   + assert (exists k', reaches p
       (Enter rho (match v with Boolean false => e3 | _ => e2 end),k) (Fault r,k')) as T.
     { destruct v; try solve [eapply IH; eauto]. destruct b; eapply IH; eauto. }
     destruct T as [k' T]; exists k'.
     eapply chain; [apply one; reflexivity|].
     eapply chain; [eapply eval_trace; exact E|].
     eapply chain; [apply one; reflexivity|exact T].
   + subst; destruct (IH p rho e1 _ E F (Choose rho e2 e3::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
   + subst; contradiction.
   + subst; destruct (IH p rho e1 _ E F (Choose rho e2 e3::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
 - destruct (eval n p rho e1) eqn:E.
   + destruct (IH p (bind rho s v) e2 r H F k) as [k' T]; exists k'.
     eapply chain; [apply one; reflexivity|].
     eapply chain; [eapply eval_trace; exact E|].
     eapply chain; [apply one; reflexivity|exact T].
   + subst; destruct (IH p rho e1 _ E F (Bind rho s e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
   + subst; contradiction.
   + subst; destruct (IH p rho e1 _ E F (Bind rho s e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
 - destruct (eval n p rho e1) eqn:E.
   + assert (eval n p rho e2 = r /\ v <> Boolean false) as [B V].
     { destruct v; try (split; [exact H|discriminate]).
       destruct b; [split; [exact H|discriminate]|subst; contradiction]. }
     destruct (IH p rho e2 r B F k) as [k' T]; exists k'.
     eapply chain; [apply one; reflexivity|].
     eapply chain; [eapply eval_trace; exact E|].
     eapply chain; [apply one; cbn [step]; destruct v; try reflexivity;
       destruct b; [reflexivity|contradiction V; reflexivity]|exact T].
   + subst; destruct (IH p rho e1 _ E F (Conjoin rho e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
   + subst; contradiction.
   + subst; destruct (IH p rho e1 _ E F (Conjoin rho e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
 - destruct (eval n p rho e1) eqn:E.
   + assert (v = Boolean false) as V.
     { destruct v; try (subst; contradiction). destruct b; [subst; contradiction|reflexivity]. }
     subst v. destruct (IH p rho e2 r H F k) as [k' T]; exists k'.
     eapply chain; [apply one; reflexivity|].
     eapply chain; [eapply eval_trace; exact E|].
     eapply chain; [apply one; reflexivity|exact T].
   + subst; destruct (IH p rho e1 _ E F (Disjoin rho e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
   + subst; contradiction.
   + subst; destruct (IH p rho e1 _ E F (Disjoin rho e2::k)) as [k' T].
     exists k'; eapply chain; [apply one; reflexivity|exact T].
 - change (match many n p rho args with
     | Values vs => match p s with
       | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
         then eval n p (arguments (params d) vs) (body d) else Unsupported
       | None => external s vs end
     | ArgumentFailure r => r end = r) in H.
   assert (START : reaches p (Enter rho (Call s args),k)
      (match args with [] => apply p s [] k
       | a::rest => (Enter rho a,Arguments rho s rest []::k) end))
     by (apply one; destruct args; reflexivity).
   destruct (many n p rho args) eqn:E.
   + assert (exists k', reaches p (apply p s vs k) (Fault r,k')) as T.
     { unfold apply. destruct (p s) as [d|] eqn:D.
       - destruct (Nat.eqb _ _) eqn:A.
         + eapply IH; eauto.
         + subst; exists k; constructor.
       - rewrite H. destruct r; try contradiction; exists k; constructor. }
     destruct T as [k' T]; exists k'. eapply chain; [exact START|].
     eapply chain; [exact (arguments_trace n p rho args vs s [] k E)|exact T].
   + subst. destruct (arguments_failure_trace n p rho (IH p rho)
       args r s [] k E F) as [k' T].
     exists k'; eapply chain; [exact START|exact T].
Qed.
Lemma step_execute : forall p a b fuel r,
 transition p a b -> execute fuel p b = r -> execute (S fuel) p a = r.
Proof.
 intros p [c k] b fuel r H E; destruct c; destruct k; cbn [execute];
 unfold transition in H; try (cbn [step] in H; discriminate);
 rewrite H; exact E.
Qed.
Theorem trace_result : forall p start finish r,
 reaches p start finish -> execute 0 p finish = r ->
 exists steps, execute steps p start = r.
Proof.
 intros p start finish r T; induction T; intros E.
 - exists 0; exact E.
 - destruct (IHT E) as [n N]. exists (S n); eapply step_execute; eauto.
Qed.
Theorem eval_failure_execute : forall fuel p rho e r,
 eval fuel p rho e = r -> failure r ->
 exists steps, execute steps p (Enter rho e,[]) = r.
Proof.
 intros fuel p rho e r E F.
 destruct (eval_failure_trace fuel p rho e r E F []) as [k T].
 eapply trace_result; [exact T|]. destruct r; try contradiction; reflexivity.
Qed.
(* The evaluator fuel counts nesting; machine fuel counts instructions. They
   are deliberately not equated. A finite trace supplies sufficient fuel. *)
Theorem trace_execute : forall p start v,
 reaches p start (Deliver v,[]) -> exists fuel, execute fuel p start = Returned v.
Proof.
 intros p start v H. remember (Deliver v,[]) as finish eqn:E.
 induction H.
 - subst; exists 0; reflexivity.
 - destruct (IHclos_refl_trans_1n E) as [fuel F].
   exists (S fuel). destruct x as [c k]; destruct c; destruct k;
     cbn [execute]; unfold transition in H; try (cbn [step] in H; discriminate).
   all: rewrite H; exact F.
Qed.
Theorem eval_execute : forall fuel p rho e v,
 eval fuel p rho e = Returned v ->
 exists steps, execute steps p (Enter rho e,[]) = Returned v.
Proof. intros; apply trace_execute; eapply eval_trace; eauto. Qed.
Theorem run_invoke : forall fuel ds name args v,
 run fuel ds name args = Returned v ->
 exists steps, invoke steps ds name args = Returned v.
Proof.
 intros fuel ds name args v H. unfold run in H.
 destruct (lookup ds name) as [d|] eqn:D; try discriminate.
 destruct (Nat.eqb _ _) eqn:A; try discriminate.
 apply eval_execute in H. destruct H as [steps H]. exists steps.
 unfold invoke; rewrite D,A; exact H.
Qed.
Theorem eval_concurrent : forall fuel p rho e v wa wb observed,
 eval fuel p rho e = Returned v ->
 concurrent_reaches p ((Enter rho e,[]),wa) ((Deliver observed,[]),wb) ->
 observed = v.
Proof.
 intros fuel p rho e v wa wb observed E C.
 apply erase_rebindings in C; cbn in C.
 pose proof (eval_trace fuel p rho e v E []) as T.
 assert ((Deliver observed,[]) = (Deliver v,[])) as H by
   (eapply terminal_unique; [exact C|exact T|reflexivity|reflexivity]).
 inversion H; reflexivity.
Qed.
Theorem eval_terminal_trace : forall fuel p rho e r,
 eval fuel p rho e = r -> r <> Exhausted -> exists finish,
 reaches p (Enter rho e,[]) finish /\ step p finish = None /\ execute 0 p finish = r.
Proof.
 intros fuel p rho e r E N. destruct r.
 - exists (Deliver v,[]); split; [eapply eval_trace; eauto|split; reflexivity].
 - destruct (eval_failure_trace fuel p rho e _ E I []) as [k T].
   exists (Fault (Raised owner message),k); split; [exact T|split; reflexivity].
 - contradiction.
 - destruct (eval_failure_trace fuel p rho e _ E I []) as [k T].
   exists (Fault Unsupported,k); split; [exact T|split; reflexivity].
Qed.
Theorem eval_result_execute : forall fuel p rho e r,
 eval fuel p rho e = r -> r <> Exhausted ->
 exists steps, execute steps p (Enter rho e,[]) = r.
Proof.
 intros. destruct (eval_terminal_trace fuel p rho e r H H0) as [finish [T [_ E]]].
 eapply trace_result; eauto.
Qed.
Theorem run_result_invoke : forall fuel ds name args r,
 run fuel ds name args = r -> r <> Exhausted ->
 exists steps, invoke steps ds name args = r.
Proof.
 intros fuel ds name args r H N. unfold run in H.
 destruct (lookup ds name) as [d|] eqn:D.
 - destruct (Nat.eqb _ _) eqn:A.
   + destruct (eval_result_execute fuel (lookup ds) (arguments (params d) args)
       (body d) r H N) as [steps E].
     exists steps; unfold invoke; rewrite D,A; exact E.
   + subst; exists 0; unfold invoke; rewrite D,A; reflexivity.
 - subst; exists 0; unfold invoke; rewrite D; reflexivity.
Qed.
Theorem eval_concurrent_result : forall fuel p rho e r wa wb finish,
 eval fuel p rho e = r -> r <> Exhausted ->
 concurrent_reaches p ((Enter rho e,[]),wa) (finish,wb) ->
 step p finish = None -> execute 0 p finish = r.
Proof.
 intros fuel p rho e r wa wb finish E N C S.
 destruct (eval_terminal_trace fuel p rho e r E N) as [target [T [ST R]]].
 apply erase_rebindings in C; cbn in C.
 assert (finish = target) by (eapply terminal_unique; eauto).
 subst; exact R.
Qed.
End NativeSimulation.
