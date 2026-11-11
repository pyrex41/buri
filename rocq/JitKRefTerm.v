(* Shen/JIT Phase 2: KTerm, the termination relation of the front passes (OB-JIT-LOWER-TERM).

   KRef (rocq/JitKRef.v) is partial correctness: every terminating run of the target e is matched
   by one of the source e0. It does not say that e terminates when e0 does. KTerm is that
   direction:

     KTerm sealed D g e0 e := JitKTerm.KRef sealed D g e e0

   where JitKTerm.KRef is KRef's relation, text for text, over `jit_rules_nr sealed`: jit_rules
   with no catchable resource failure (rocq/JitKTerm.v says exactly what differs). Read with the
   arguments the other way round, its index counts SOURCE steps, and KTerm g e0 e says: from any
   environments related on g, any related stores meeting D and any related continuations, every
   resource-free run of the source e0 that reaches a terminal state (a value, an exception, or a
   wrong state), after any IO trace, is matched by a resource-free run of the target e with the
   same trace to a terminal state of the same kind: a related value and store, the same
   exception and a related store, or a wrong state. So a target that diverges, or ends only in a
   resource failure, has a source that does too: by contraposition, constructively
   (JitKRefTermThm.KTerm_diverges).

   Why the resource-free rules. Under jit_rules, step_r_resource lets ANY running state raise
   (XUser "out of memory"), so "the target reaches a terminal state" would be met by a resource
   raise, and KRef read backwards would say nothing about termination. KTerm_omega_refuted below
   is the witness: a source that raises (simple-error "out of memory") is NOT KTerm-refined by a
   target that loops (omega), which under jit_rules it would be. Mutant
   ShenJitKTermResourceSteps gives jit_rules_nr jit_rules' resource field back, and Rocq must then
   reject KTerm_omega_refuted. A resource-free run is also a jit_rules run (step_nr_sub), so what
   KTerm promises about the target is a promise about the real port's semantics too.

   Total correctness is the pair: KTerm for termination and outcome in the resource-free
   semantics, KRef for every jit_rules run of the target (including resource raises). Each is
   per link; neither uses transitivity of a step-indexed relation.

   This file holds the definition, its link to jit_rules, the non-vacuity theorem, and the
   statements still open (each *_statement below, with a ledger line in OB-JIT-LOWER-TERM). The
   fundamental property, every compatibility lemma and the per-rewrite lemmas, in KTerm's
   orientation, are in rocq/JitKRefTermThm.v.

   Does NOT say:
   - anything about runs that use step_r_resource: a source run that catches an "out of memory"
     and then returns is not one KTerm speaks of;
   - that the target takes comparable numbers of steps (it may take any number, including more:
     share's freeze/thaw);
   - anything about a source that diverges;
   - anything about the emitted bytecode: binding KTerm to the extended back end's invariant
     (JitEmitInv, on p2/emit-spec and not on p2/int) is open, and recorded as such in the
     OB-JIT-LOWER-TERM ledger entry; no statement for it is written here, because the invariant it
     would name is not on this branch. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKTerm JitKTermGround.
Import ListNotations.
Module JitKRefTerm.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitKTerm.JitKTerm.

(* ---------- the relation ---------- *)
Definition KTerm (sealed : list name) (D : list (name * fundef)) (g : list name) (e0 e : expr) : Prop :=
 JitKTerm.JitKTerm.KRef sealed D g e e0.

(* ---------- resource-free runs are jit_rules runs ---------- *)
(* jit_rules_nr and jit_rules agree on every field but resource_exn, so the machine agrees on
   every control but Fail. eq_depth_r takes the rules as an argument of its fixpoint, so it is
   compared by induction (as KLPort.eq_depth_r_agreed is), not by conversion. The tactics below
   tolerate goals that conversion already closes, so that mutant ShenJitKTermResourceSteps (where
   the two rule records are the same term) is rejected at om_srun, not here. *)
Lemma eq_depth_r_same_id : forall R1 R2 P h d a b, object_identity R1 = object_identity R2 ->
 eq_depth_r R1 P h d a b = eq_depth_r R2 P h d a b.
Proof.
 intros R1 R2 P h d a b O. revert a b. induction d as [|d IH]; intros a b; [reflexivity|].
 assert (L : forall xs ys, list_eq (eq_depth_r R1 P h d) xs ys = list_eq (eq_depth_r R2 P h d) xs ys).
 { induction xs as [|x xs IHx]; destruct ys as [|y ys]; cbn; try reflexivity.
   rewrite IH. destruct (eq_depth_r R2 P h d x y) as [[|]|]; try reflexivity. apply IHx. }
 revert b. induction a; intro w; destruct w; cbn; try reflexivity; try (unfold eq_opaque_r; rewrite O; reflexivity).
 - change (match eq_depth_r R1 P h (S d) a1 w1 with Some true => eq_depth_r R1 P h (S d) a2 w2 | r => r end
     = match eq_depth_r R2 P h (S d) a1 w1 with Some true => eq_depth_r R2 P h (S d) a2 w2 | r => r end).
   rewrite IHa1, IHa2. reflexivity.
 - destruct (Nat.eqb l l0); [reflexivity|].
   destruct (nth_error h l), (nth_error h l0); try reflexivity. apply L.
Qed.

Lemma eq_depth_r_nr : forall sealed P h d a b,
 eq_depth_r (jit_rules_nr sealed) P h d a b = eq_depth_r (jit_rules sealed) P h d a b.
Proof. intros. apply eq_depth_r_same_id. reflexivity. Qed.

Lemma prim_rule_r_nr : forall sealed P p args s,
 prim_rule_r (jit_rules_nr sealed) P p args s = prim_rule_r (jit_rules sealed) P p args s.
Proof.
 intros sealed P p args s. destruct p; try reflexivity;
 unfold prim_rule_r, rule_equal_r, kl_eq_r; destruct args as [|a [|b [|c rest]]]; try reflexivity;
 rewrite eq_depth_r_nr; reflexivity.
Qed.

Lemma call_named_r_nr : forall sealed P g args k s,
 call_named_r (jit_rules_nr sealed) P g args k s = call_named_r (jit_rules sealed) P g args k s.
Proof.
 intros sealed P g args k s. unfold call_named_r, prim_move_r.
 destruct (lookup g (gfuns s)) as [[p|ps b]|]; try reflexivity; rewrite prim_rule_r_nr; reflexivity.
Qed.

Lemma apply_value_r_nr : forall sealed P f args k s,
 apply_value_r (jit_rules_nr sealed) P f args k s = apply_value_r (jit_rules sealed) P f args k s.
Proof.
 intros sealed P f args k s. unfold apply_value_r. destruct f; try reflexivity; apply call_named_r_nr.
Qed.

Lemma next_r_nr : forall sealed P c, (forall r, ctl c <> Fail r) ->
 next_r (jit_rules_nr sealed) P c = next_r (jit_rules sealed) P c.
Proof.
 intros sealed P [c0 k s] NF. destruct c0 as [rho e|v|x|r|ev|why]; try reflexivity.
 all: lazymatch goal with
 | |- next_r _ _ (Cfg (Eval _ ?e) _ _) = _ =>
     unfold next_r; cbn [ctl kont mem]; unfold eval_move_r; destruct e; try reflexivity;
     destruct args; [apply call_named_r_nr|reflexivity]
 | |- next_r _ _ (Cfg (Ret _) ?k _) = _ =>
     unfold next_r; cbn [ctl kont mem]; destruct k as [|f k]; [reflexivity|];
     unfold ret_move_r; destruct f; try reflexivity;
     first [destruct args; [apply apply_value_r_nr|reflexivity]
           |destruct rest; [first [apply apply_value_r_nr|apply call_named_r_nr]|reflexivity]
           |apply apply_value_r_nr]
 | |- next_r _ _ (Cfg (Fail ?r) _ _) = _ => exfalso; exact (NF r eq_refl)
 end.
Qed.

(* The proof below is written so that it also goes through when jit_rules_nr's resource field is
   jit_rules' own (mutant ShenJitKTermResourceSteps): step_nr_sub is not where that mutant must be
   rejected; om_srun, KTerm's non-vacuity, is. *)
Theorem step_nr_sub : forall sealed P c l c',
 step_r (jit_rules_nr sealed) P c l c' -> step_r (jit_rules sealed) P c l c'.
Proof.
 intros sealed P c l c' H. destruct H as [c c' E|c q kk r0 E|c r0 x Rs Rx].
 - apply step_r_tau. destruct c as [[rho e|v|x|r|ev|why] k s];
     try (rewrite <- next_r_nr; [exact E|intros r' N; discriminate N]).
   destruct r; cbn in E |- *; first [discriminate E|exact E].
 - apply step_r_io. destruct c as [[rho e|v|x|r|ev|why] k s];
     try (rewrite <- next_r_nr; [exact E|intros r' N; discriminate N]).
   destruct r; cbn in E |- *; first [discriminate E|exact E].
 - first [destruct r0; discriminate Rx|exact (step_r_resource (jit_rules sealed) P c r0 x Rs Rx)].
Qed.

Theorem srun_nr_sub : forall sealed c t c',
 JitKTerm.JitKTerm.srun sealed c t c' -> star (step_r (jit_rules sealed) jit_profile) c t c'.
Proof.
 intros sealed c t c' H. unfold JitKTerm.JitKTerm.srun in H.
 induction H as [c|c l c1 t c2 St _ IH]; [constructor|]. econstructor; [apply step_nr_sub; exact St|exact IH].
Qed.

(* ---------- non-vacuity ---------- *)
(* omega = ((lambda x (x x)) (lambda x (x x))): a loop with no IO. Every lambda allocates a cell,
   so no configuration repeats; OmInv is the set of configurations it passes through. *)
Definition om_x : name := of_string "x".
Definition om_body : expr := EApp (EVar om_x) [EVar om_x].
Definition om_lam : expr := ELam om_x om_body.
Definition omega : expr := EApp om_lam [om_lam].
Definition lamB (v : value) : Prop := exists r, v = VLam om_x om_body r.

Inductive OmInv : config -> Prop :=
 | om1 rho s : OmInv (Cfg (Eval rho omega) [] s)
 | om2 rho s : OmInv (Cfg (Eval rho om_lam) [KHead [om_lam] rho] s)
 | om3 rho v s : lamB v -> OmInv (Cfg (Ret v) [KHead [om_lam] rho] s)
 | om4 rho v s : lamB v -> OmInv (Cfg (Eval rho om_lam) [KArgs v [] [] rho] s)
 | om5 rho u v s : lamB u -> lamB v -> OmInv (Cfg (Ret u) [KArgs v [] [] rho] s)
 | om6 rho u s : lamB u -> lookup om_x rho = Some u -> OmInv (Cfg (Eval rho om_body) [] s)
 | om7 rho u s : lamB u -> lookup om_x rho = Some u -> OmInv (Cfg (Eval rho (EVar om_x)) [KHead [EVar om_x] rho] s)
 | om8 rho u v s : lamB u -> lamB v -> lookup om_x rho = Some u -> OmInv (Cfg (Ret v) [KHead [EVar om_x] rho] s)
 | om9 rho u v s : lamB u -> lamB v -> lookup om_x rho = Some u -> OmInv (Cfg (Eval rho (EVar om_x)) [KArgs v [] [] rho] s).

Lemma lamB_tagged : forall rho s, lamB (VLam om_x om_body (tagged_env rho s)).
Proof. intros. eexists; reflexivity. Qed.

Lemma om_var_next : forall sealed rho u K s, lookup om_x rho = Some u ->
 next_r (jit_rules_nr sealed) jit_profile (Cfg (Eval rho (EVar om_x)) K s) = MTau (Cfg (Ret u) K s).
Proof.
 intros sealed rho u K s E.
 change (MTau (Cfg (match lookup om_x rho with Some v => Ret v | None => Throw (XUnboundVar om_x) end) K s)
   = MTau (Cfg (Ret u) K s)).
 rewrite E. reflexivity.
Qed.

Lemma om_step : forall sealed c, OmInv c ->
 exists c', next_r (jit_rules_nr sealed) jit_profile c = MTau c' /\ OmInv c'.
Proof.
 intros sealed c H. destruct H.
 - eexists; split; [reflexivity|apply om2].
 - eexists; split; [reflexivity|apply om3; apply lamB_tagged].
 - eexists; split; [reflexivity|apply om4; assumption].
 - eexists; split; [reflexivity|apply om5; [apply lamB_tagged|assumption]].
 - destruct H0 as [r ->]. eexists; split; [reflexivity|]. apply (om6 _ u); [exact H|reflexivity].
 - eexists; split; [reflexivity|]. apply (om7 _ u); assumption.
 - eexists; split; [apply om_var_next; exact H0|]. apply (om8 _ u); assumption.
 - eexists; split; [reflexivity|]. apply (om9 _ u); assumption.
 - eexists; split; [apply om_var_next; exact H1|]. apply om5; assumption.
Qed.

Lemma om_srun : forall sealed c t c', JitKTerm.JitKTerm.srun sealed c t c' -> OmInv c -> OmInv c'.
Proof.
 intros sealed c t c' H. unfold JitKTerm.JitKTerm.srun in H.
 induction H as [c|c l c1 t c2 St _ IH]; intro I; [exact I|]. apply IH.
 destruct (om_step sealed c I) as (c' & E & I').
 destruct St as [c c1 E1|c q kk r E1|c r x _ Rx].
 - rewrite E in E1. injection E1 as <-. exact I'.
 - rewrite E in E1. discriminate.
 - destruct r; discriminate.
Qed.

(* The source: (simple-error "out of memory"), in a store whose only function is simple-error. *)
Definition oom_text : text := of_string "out of memory".
Definition e_oom : expr := ECall (of_string "simple-error") [EStr oom_text].
Definition st_oom : store := Store [] [] [(of_string "simple-error", FPrim PSimpleError)].

Lemma runs_tau : forall sealed n c c1 t c',
 next_r (jit_rules_nr sealed) jit_profile c = MTau c1 -> JitKTerm.JitKTerm.runs sealed n c1 t c' ->
 JitKTerm.JitKTerm.runs sealed (S n) c t c'.
Proof.
 intros sealed n c c1 t c' E H. change t with (trace_of Tau ++ t).
 econstructor; [apply step_r_tau; exact E|exact H].
Qed.

Lemma e_oom_runs : forall sealed,
 JitKTerm.JitKTerm.runs sealed 3 (Cfg (Eval [] e_oom) [] st_oom) [] (Cfg (Throw (XUser oom_text)) [] st_oom).
Proof.
 intro sealed.
 eapply runs_tau; [reflexivity|]. eapply runs_tau; [reflexivity|]. eapply runs_tau; [reflexivity|].
 constructor.
Qed.

(* KTerm is not vacuous: a looping target does not refine a source that raises, even when the
   exception is the one a resource failure would raise. Under jit_rules it would: the loop can
   raise (XUser "out of memory") by step_r_resource at any running state. *)
Theorem KTerm_omega_refuted : forall sealed, ~ KTerm sealed [] [] e_oom omega.
Proof.
 intros sealed H. unfold KTerm, JitKTerm.JitKTerm.KRef in H.
 assert (W : wf_world []) by (split; constructor).
 specialize (H 4 [] [] [] W (fun x I => match I with end)).
 assert (HK : JitKTerm.JitKTerm.KRel sealed [] 4 [] [] []) by (apply JitKTermGround.JitKTermGround.KRel_top; exact W).
 assert (HS : JitKTerm.JitKTerm.SRel_with [] (JitKTerm.JitKTerm.VRelF sealed [] 4 4) [] st_oom st_oom).
 { split; [exact W|]. split; [intros f d []|]. split; [intros f d []|].
   split; [reflexivity|]. split; [constructor|]. intros l0 l []. }
 specialize (H 4 (le_n 4) [] (conj (fun a I => I) W) [] [] HK st_oom st_oom HS).
 destruct (H 3 [] _ ltac:(lia) (e_oom_runs sealed)) as (_ & Hx & _).
 destruct (Hx (XUser oom_text) st_oom eq_refl) as (s0 & w' & Sr & _).
 assert (I := om_srun sealed _ _ _ Sr (om1 [] st_oom)). inversion I.
Qed.

(* ======================= statements (OB-JIT-LOWER-TERM) ======================= *)
(* No proof here. KTerm_compose_statement is proved as JitKRefTermThm.KTerm_compose;
   KTerm_checker_statement is open (no front-link checker exists yet), and the ledger names it. *)

(* The two front links compose for termination: from KTerm for share (b0 to b1) and for norm (b1
   to e), a resource-free source run of b0 to a first-order value or an exception, from a store
   meeting D, is matched by a resource-free run of e to the same value or exception, with
   GStore-related stores. The composition goes through the closed first-order observation, as
   KRef's does (GStore_trans), never through transitivity of KTerm. *)
Definition KTerm_compose_statement (sealed : list name) (D : list (name * fundef)) : Prop :=
 forall g b0 b1 e rho s,
 JitKTerm.JitKTerm.D_wf sealed D -> KTerm sealed D g b0 b1 -> KTerm sealed D g b1 e ->
 Forall (fun p => JitKTerm.JitKTerm.fo (snd p)) rho -> (forall x, In x g -> exists v, lookup x rho = Some v) ->
 JitKTerm.JitKTerm.StoreHas D s -> store_ok s ->
 (forall v s0, JitKTerm.JitKTerm.srun sealed (Cfg (Eval rho b0) [] s) [] (Cfg (Ret v) [] s0) -> JitKTerm.JitKTerm.fo v ->
    exists s' w, JitKTerm.JitKTerm.srun sealed (Cfg (Eval rho e) [] s) [] (Cfg (Ret v) [] s') /\
      JitKTerm.JitKTerm.wext (JitKTerm.JitKTerm.id_world s) w /\
      JitKTerm.JitKTerm.GStore w s' s0) /\
 (forall x s0, JitKTerm.JitKTerm.srun sealed (Cfg (Eval rho b0) [] s) [] (Cfg (Throw x) [] s0) ->
    exists s' w, JitKTerm.JitKTerm.srun sealed (Cfg (Eval rho e) [] s) [] (Cfg (Throw x) [] s') /\
      JitKTerm.JitKTerm.wext (JitKTerm.JitKTerm.id_world s) w /\
      JitKTerm.JitKTerm.GStore w s' s0).

(* Front-link checkers establish KTerm: for each front rule the checker accepts, the rule's
   source anti-reduction (KRef's ERel_anti_* family) has a KTerm counterpart as a source
   REDUCTION (JitKRefTermThm.ERel_red_* family). Stated per checker when the checkers land
   (share, norm: OB-JIT-LOWER-FRONT); here, the statement form for a checker `chk`. *)
Definition KTerm_checker_statement (sealed : list name) (D : list (name * fundef))
 (chk : list name -> expr -> expr -> bool) : Prop :=
 forall g e0 e, JitKTerm.JitKTerm.D_wf sealed D -> chk g e0 e = true -> KTerm sealed D g e0 e.
End JitKRefTerm.
