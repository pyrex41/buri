(* E2E-06 metatheory: determinism, progress and the exact stuck states, the
   closed system with an environment oracle, a fuel evaluator proved sound,
   monotone and complete for terminating runs, and the separation of fuel
   exhaustion from divergence. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics.
Import ListNotations.
Module KLMetatheory.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.

Definition running (m : move) : Prop := match m with MTau _ | MIO _ _ => True | _ => False end.

Lemma prim_move_running : forall P p args rest k s, running (prim_move P p args rest k s).
Proof. intros; unfold prim_move; destruct (prim_rule P p args s); exact I. Qed.
Lemma call_named_running : forall P g args k s, running (call_named P g args k s).
Proof.
 intros; unfold call_named; destruct (lookup g (gfuns s)) as [[p|ps b]|]; cbn; try exact I;
 match goal with |- context [if ?b then _ else _] => destruct b end; try exact I; apply prim_move_running.
Qed.
Lemma apply_value_running : forall P f args k s, running (apply_value P f args k s).
Proof.
 intros; unfold apply_value; destruct f; try exact I; destruct args; try exact I;
 apply call_named_running.
Qed.
Lemma eval_move_running : forall P rho e k s, running (eval_move P rho e k s).
Proof.
 intros; destruct e; cbn; try exact I.
 - destruct clauses as [|[c b] rest]; exact I.
 - destruct (nodupb params); exact I.
 - destruct args; [apply call_named_running|exact I].
Qed.
Lemma ret_move_running : forall P v f k s, running (ret_move P v f k s).
Proof.
 intros; destruct f; cbn; try exact I;
 try (destruct v; try exact I; destruct b0; exact I);
 try (destruct v; try exact I; destruct b; exact I).
 - destruct args; [apply apply_value_running|exact I].
 - destruct rest; [apply apply_value_running|exact I].
 - destruct rest; [apply call_named_running|exact I].
 - apply apply_value_running.
Qed.
Lemma throw_move_running : forall x f k s, running (throw_move x f k s).
Proof. intros; destruct f; exact I. Qed.

(* Exact final configurations. *)
Theorem final_iff : forall P c o, final P c o <->
 (exists v, ctl c = Ret v /\ kont c = [] /\ o = Normal v) \/
 (exists x, ctl c = Throw x /\ kont c = [] /\ o = Error x) \/
 (exists r, ctl c = Fail r /\ o = ResourceOut r) \/
 (exists sg, ctl c = Halted (Signal sg) /\ o = Killed sg) \/
 (ctl c = Halted Cancel /\ o = Cancelled).
Proof.
 intros P [ctl k s] o; unfold final, next; cbn; split.
 - destruct ctl.
   + intro H; pose proof (eval_move_running P rho e k s) as R; rewrite H in R; contradiction.
   + destruct k as [|f k]; [intro H; inversion H; subst; left; eauto|].
     intro H; pose proof (ret_move_running P v f k s) as R; rewrite H in R; contradiction.
   + destruct k as [|f k]; [intro H; inversion H; subst; right; left; eauto|].
     intro H; pose proof (throw_move_running x f k s) as R; rewrite H in R; contradiction.
   + intro H; inversion H; subst; right; right; left; eauto.
   + destruct ev; intro H; inversion H; subst; [right; right; right; left; eauto|right; right; right; right; auto].
   + discriminate.
 - intros [[v [E1 [E2 E3]]]|[[x [E1 [E2 E3]]]|[[r [E1 E2]]|[[sg [E1 E2]]|[E1 E2]]]]]; subst; reflexivity.
Qed.

(* Progress: every configuration steps internally, awaits the environment,
   is final, or is an explicit Wrong state. *)
Theorem progress : forall P c,
 (exists c', step P c Tau c') \/
 (exists q kk, forall r, step P c (Obs (EvIO q r)) (kk r)) \/
 (exists o, final P c o) \/ wrong P c.
Proof.
 intros P c; destruct (next P c) eqn:E.
 - left; exists c0; constructor; exact E.
 - right; left; exists q, k; intro r; constructor; exact E.
 - right; right; left; exists o; exact E.
 - right; right; right; exists why; exact E.
Qed.

Theorem wrong_iff : forall P c, wrong P c <-> exists w, ctl c = Wrong w.
Proof.
 intros P [ctl k s]; unfold wrong, next; cbn; split; intros [w H].
 - destruct ctl.
   + pose proof (eval_move_running P rho e k s) as R; rewrite H in R; contradiction.
   + destruct k as [|f k]; [discriminate|].
     pose proof (ret_move_running P v f k s) as R; rewrite H in R; contradiction.
   + destruct k as [|f k]; [discriminate|].
     pose proof (throw_move_running x f k s) as R; rewrite H in R; contradiction.
   + discriminate.
   + destruct ev; discriminate.
   + inversion H; subst; eauto.
 - subst; eauto.
Qed.

(* Explicit stuck-state characterization: a configuration with no step that is
   not final is exactly a Wrong state. The only producers of Wrong are the
   enumerated profile-undefined operations (rule_equal on undefined equality,
   and dangling locations, which well-formed states exclude). *)
Theorem stuck_iff_wrong : forall P c,
 ((forall l c', ~ step P c l c') /\ (forall o, ~ final P c o)) <-> exists w, ctl c = Wrong w.
Proof.
 intros P c; split.
 - intros [N F]. apply (proj1 (wrong_iff P c)).
   destruct (progress P c) as [[c' S]|[[q [kk S]]|[[o Fo]|W]]].
   + destruct (N _ _ S).
   + destruct (N _ _ (S RClosed)).
   + destruct (F _ Fo).
   + exact W.
 - intro H; apply (proj2 (wrong_iff P c)) in H as [w H]; split.
   + intros l c' S; inversion S; subst; congruence.
   + intros o F; unfold final in F; congruence.
Qed.

(* Determinism of the open relation: the request is determined by the state;
   the successor is determined by the state and the environment's response. *)
Theorem step_deterministic : forall P c l1 c1 l2 c2,
 step P c l1 c1 -> step P c l2 c2 ->
 (l1 = Tau /\ l2 = Tau /\ c1 = c2) \/
 (exists q r1 r2, l1 = Obs (EvIO q r1) /\ l2 = Obs (EvIO q r2) /\ (r1 = r2 -> c1 = c2)).
Proof.
 intros P c l1 c1 l2 c2 S1 S2; inversion S1; subst; inversion S2; subst; try congruence.
 - left; split; [reflexivity|split; [reflexivity|congruence]].
 - right. rewrite H in H0; inversion H0; subst. exists q0, r, r0; repeat split; intro; subst; reflexivity.
Qed.

Lemma final_no_step : forall P c o l c', final P c o -> ~ step P c l c'.
Proof. intros P c o l c' F S; unfold final in F; inversion S; congruence. Qed.

(* ---------- closed system: program plus environment oracle ---------- *)
Section Closed.
Variable W : Type.
(* The environment answers requests (possibly nondeterministically), may have
   a pending signal or cancellation, and advances on internal steps (time). *)
Variable O : W -> request -> response -> W -> Prop.
Variable pending : W -> option env_event.
Variable tick : W -> W.
Variable P : profile.

Definition cstate := (config * W)%type.
Inductive cstep : cstate -> label -> cstate -> Prop :=
 | cs_tau c c' w : pending w = None -> next P c = MTau c' -> cstep (c, w) Tau (c', tick w)
 | cs_io c q kk r w w' : pending w = None -> next P c = MIO q kk -> O w q r w' ->
     cstep (c, w) (Obs (EvIO q r)) (kk r, w')
 | cs_env c w ev : pending w = Some ev -> running (next P c) ->
     cstep (c, w) (Obs (EvEnv ev)) (Cfg (Halted ev) (kont c) (mem c), w).
Definition cfinal (cw : cstate) (o : kl_outcome) := final P (fst cw) o.

Definition oracle_deterministic := forall w q r1 w1 r2 w2,
 O w q r1 w1 -> O w q r2 w2 -> r1 = r2 /\ w1 = w2.

Theorem closed_deterministic : oracle_deterministic -> deterministic cstep.
Proof.
 intros D cw l1 s1 l2 s2 S1 S2; inversion S1; subst; inversion S2; subst; try congruence.
 all: repeat match goal with
   | H1 : next P ?c = _, H2 : next P ?c = _ |- _ => rewrite H1 in H2; inversion H2; subst; clear H2
   | H1 : pending ?w = _, H2 : pending ?w = _ |- _ => rewrite H1 in H2; inversion H2; subst; clear H2
   end.
 all: try (split; reflexivity).
 match goal with HO1 : O ?w ?q ?r1 ?w1, HO2 : O ?w ?q ?r2 ?w2 |- _ =>
   destruct (D _ _ _ _ _ _ HO1 HO2); subst; auto end.
Qed.

Lemma closed_final_inert : final_inert cstep cfinal.
Proof.
 intros [c w] o l s' F S; unfold cfinal, final in F; cbn in F.
 inversion S; subst; try congruence.
 match goal with H : running _ |- _ => rewrite F in H; exact H end.
Qed.

Lemma closed_final_unique : final_unique cfinal.
Proof. intros [c w] o1 o2 F1 F2; unfold cfinal, final in *; cbn in *; congruence. Qed.

Definition behaviors (c : config) (w : W) := behaves cstep cfinal (c, w).

Theorem closed_terminates_excludes_divergence : oracle_deterministic ->
 forall c w t o t', behaviors c w (Terminates t o) -> ~ behaviors c w (Diverges t').
Proof.
 intros D c w t o t'.
 apply (terminates_excludes_divergence cstate value exn cstep cfinal
   (closed_deterministic D) closed_final_inert).
Qed.

Theorem closed_terminates_unique : oracle_deterministic ->
 forall c w t1 o1 t2 o2, behaviors c w (Terminates t1 o1) -> behaviors c w (Terminates t2 o2) ->
 t1 = t2 /\ o1 = o2.
Proof.
 intros D c w.
 apply (terminates_unique cstate value exn cstep cfinal
   (closed_deterministic D) closed_final_inert closed_final_unique).
Qed.
End Closed.

(* ---------- fuel evaluator against a deterministic oracle ---------- *)
Section Run.
Variable W : Type.
Variable respond : W -> request -> response * W.
Variable pending : W -> option env_event.
Variable tick : W -> W.
Variable P : profile.
Definition graph (w : W) (q : request) (r : response) (w' : W) := respond w q = (r, w').
Definition rstep := cstep W graph pending tick P.

Definition cnext (c : config) (w : W) : option (label * config * W) :=
 match next P c with
 | MTau c' => Some (match pending w with
     | Some ev => (Obs (EvEnv ev), Cfg (Halted ev) (kont c) (mem c), w)
     | None => (Tau, c', tick w) end)
 | MIO q kk => Some (match pending w with
     | Some ev => (Obs (EvEnv ev), Cfg (Halted ev) (kont c) (mem c), w)
     | None => let (r, w') := respond w q in (Obs (EvIO q r), kk r, w') end)
 | _ => None end.

Lemma cnext_sound : forall c w l c' w', cnext c w = Some (l, c', w') -> rstep (c, w) l (c', w').
Proof.
 intros c w l c' w'; unfold cnext; destruct (next P c) eqn:E; try discriminate;
 destruct (pending w) eqn:Pw; intro H; inversion H; subst.
 - apply cs_env; [exact Pw|rewrite E; exact I].
 - apply cs_tau; assumption.
 - apply cs_env; [exact Pw|rewrite E; exact I].
 - destruct (respond w q) as [r w2] eqn:R; inversion H; subst.
   eapply cs_io; [exact Pw|exact E|exact R].
Qed.

Lemma cnext_complete : forall c w l c' w', rstep (c, w) l (c', w') -> cnext c w = Some (l, c', w').
Proof.
 intros c w l c' w' S; inversion S; subst; unfold cnext; unfold graph in *.
 all: repeat match goal with
   | H : next P _ = _ |- _ => rewrite H; clear H
   | H : pending _ = _ |- _ => rewrite H; clear H
   | H : respond _ _ = _ |- _ => rewrite H; clear H end.
 all: try reflexivity.
 destruct (next P c); try contradiction; reflexivity.
Qed.

Definition add_trace (t : trace) (v : verdict value exn) : verdict value exn := match v with
 | VDone u o => VDone (t ++ u) o
 | VWrong u => VWrong (t ++ u)
 | VExhausted u => VExhausted (t ++ u)
 | other => other end.

Fixpoint run (fuel : nat) (c : config) (w : W) : verdict value exn :=
 match next P c with
 | MFinal o => VDone [] o
 | MWrong _ => VWrong []
 | _ => match fuel with
   | O => VExhausted []
   | S n => match cnext c w with
     | Some (l, c', w') => add_trace (trace_of l) (run n c' w')
     | None => VExhausted [] end end end.

Definition cstuck (cw : config * W) := stuck rstep (cfinal W P) cw.

Lemma wrong_cstuck : forall c w why, next P c = MWrong why -> cstuck (c, w).
Proof.
 intros c w why E; split.
 - intros l s' S; inversion S; subst; try congruence.
   match goal with H : running _ |- _ => rewrite E in H; exact H end.
 - intros o F; unfold cfinal, final in F; cbn in F; congruence.
Qed.

(* Soundness: every evaluator answer is witnessed by the small-step closed
   semantics; exhaustion witnesses only the trace prefix already executed. *)
Theorem run_sound : forall n c w,
 match run n c w with
 | VDone t o => exists c' w', star rstep (c, w) t (c', w') /\ cfinal W P (c', w') o
 | VWrong t => exists c' w', star rstep (c, w) t (c', w') /\ cstuck (c', w')
 | VExhausted t => exists c' w', star rstep (c, w) t (c', w')
 | _ => False end.
Proof.
 induction n as [|n IH]; intros c w; cbn [run].
 - destruct (next P c) eqn:E.
   + exists c, w; constructor.
   + exists c, w; constructor.
   + exists c, w; split; [constructor|exact E].
   + exists c, w; split; [constructor|eapply wrong_cstuck; eauto].
 - destruct (next P c) eqn:E;
   try (exists c, w; split; [constructor|first [exact E|eapply wrong_cstuck; eauto]]).
   all: destruct (cnext c w) as [[[l c'] w']|] eqn:N; [|exists c, w; constructor].
   all: pose proof (cnext_sound _ _ _ _ _ N) as St; specialize (IH c' w').
   all: destruct (run n c' w'); cbn; try contradiction;
        destruct IH as [c2 [w2 IH]];
        try (destruct IH as [A B]; exists c2, w2; split; [econstructor; eauto|exact B]);
        try (exists c2, w2; econstructor; eauto).
Qed.

Definition decided (v : verdict value exn) := match v with VDone _ _ | VWrong _ => True | _ => False end.

Lemma add_trace_decided : forall t v, decided (add_trace t v) <-> decided v.
Proof. intros t v; destruct v; cbn; tauto. Qed.

(* Fuel monotonicity: once decided, more fuel gives the same answer. *)
Theorem run_monotone : forall n m c w, n <= m -> decided (run n c w) -> run m c w = run n c w.
Proof.
 induction n as [|n IH]; intros m c w L D; cbn [run] in *.
 - destruct m; cbn [run]; [reflexivity|].
   destruct (next P c); cbn in D; try contradiction; reflexivity.
 - destruct m as [|m]; [lia|]. cbn [run].
   destruct (next P c); try reflexivity.
   all: destruct (cnext c w) as [[[l c'] w']|]; [|cbn in D; contradiction].
   all: rewrite (IH m c' w'); [reflexivity|lia|apply add_trace_decided in D; exact D].
Qed.

Lemma run_shape : forall n c w,
 (exists t o, run n c w = VDone t o) \/ (exists t, run n c w = VWrong t) \/ (exists t, run n c w = VExhausted t).
Proof.
 intros n c w; pose proof (run_sound n c w) as H; destruct (run n c w); eauto; contradiction.
Qed.

(* Fuel exhaustion never implies divergence; divergence implies exhaustion at
   every fuel bound (an evaluator cannot report a diverging program as done). *)
Theorem divergence_exhausts_every_fuel : forall c w t,
 behaves rstep (cfinal W P) (c, w) (Diverges t) ->
 forall n, exists u, run n c w = VExhausted u.
Proof.
 intros c w t B n. pose proof (run_sound n c w) as H.
 assert (D : deterministic rstep).
 { apply closed_deterministic. intros w0 q r1 w1 r2 w2 A1 A2; unfold graph in *; rewrite A1 in A2; inversion A2; auto. }
 destruct (run n c w) eqn:R; try contradiction; eauto.
 - destruct H as [c' [w' [A F]]].
   exfalso; eapply (terminates_excludes_divergence (config * W)%type value exn rstep (cfinal W P) D
     (closed_final_inert W graph pending tick P)); [econstructor; eauto|exact B].
 - destruct H as [c' [w' [A K]]].
   exfalso; eapply (wrong_excludes_divergence (config * W)%type value exn rstep (cfinal W P) D);
     [econstructor; eauto|exact B].
Qed.

(* Completeness within sufficient fuel: every terminating closed behavior is
   found by the evaluator. *)
Lemma star_run : forall cw t cw', star rstep cw t cw' ->
 forall c w c' w' o, cw = (c, w) -> cw' = (c', w') -> next P c' = MFinal o ->
 exists n, run n c w = VDone t o.
Proof.
 intros cw t cw' A; induction A as [s|s l s1 t s2 St A IH]; intros c w c' w' o E1 E2 F; subst.
 - inversion E2; subst; exists 0; cbn; rewrite F; reflexivity.
 - destruct s1 as [c1 w1].
   destruct (IH c1 w1 c' w' o eq_refl eq_refl F) as [n R].
   exists (S n); cbn [run].
   pose proof (cnext_complete _ _ _ _ _ St) as N.
   assert (Run : running (next P c)) by
     (inversion St; subst; repeat match goal with H : next P _ = _ |- _ => rewrite H end;
      first [exact I | assumption]).
   destruct (next P c); try contradiction; rewrite N, R; reflexivity.
Qed.

Theorem run_complete : forall c w t o,
 behaves rstep (cfinal W P) (c, w) (Terminates t o) -> exists n, run n c w = VDone t o.
Proof.
 intros c w t o B; inversion B as [t0 [c' w'] o0 A F| | |]; subst.
 eapply star_run; eauto.
Qed.
End Run.
End KLMetatheory.
