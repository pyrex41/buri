(* Shen/JIT Phase 2: KRef's structural lemmas (kref-base). The statements VRel_down_statement,
   VRel_wext_statement, ERel_down_statement, sealed_stable_statement and storehas_stable_statement
   are JitKRef.v's; this file proves them, and adds the lemmas the compatibility files build on.
   It re-opens Section Equiv with JitKRef.v's Variables and the abbreviations of JitKRefGround.v.
   No Definition here changes a JitKRef statement; the helper Definitions (ObsTr, nonterm, nontrap,
   swap_ok, AppRel, AppAll, sval, vptrs) are used by lemma statements only.

   What is proved (every Theorem and Corollary is in Audit_Jit and prints "Closed under the global context"):
   - Index and world structure. VRel_down, VRel_wext, ERel_down, KRef_scope (JitKRef statements); SRel,
     KRel, ERel, EnvRel down in the index; KRel, ERel, EnvRel up in wext; ObsT down in the index
     and ANTITONE in the world (ObsT_wext_anti). Two directions the task listed are false and are
     refuted in Rocq instead: SRel is not monotone up in wext (SRel_wext_refuted: a new pair needs
     its cells; SRel_wext_cells is the true form), and ObsT is not (ObsT_wext_refuted).
   - Observation. ObsTr, ObsT with a source trace prefix (ObsT is its [] case); source
     anti-reduction ObsT_anti (tau prefix) and ObsT_anti_io (any prefix, traces concatenate);
     target-step reduction ObsT_step (every target step, matched with its trace, at one index
     less) and its running-state form ObsT_running, where a target resource step is matched by the
     source's own (resource_match, through KRel's Throw clause); wrong_match.
   - ERel-form anti-reduction: ERel_anti (the source steps silently to a related configuration,
     possibly with a new environment and a store with one-sided cells), and its instances for let,
     if, cond, type, a named call of a D function, and lambda application (the ERel_anti_ lemmas).
   - Frames: ERel_push (the first step of a compound form pushes a frame: the bind lemma), the
     Throw clause for every non-trap frame at once (KRel_throw_frame), KRel_push, and one KRel lemma
     per frame kind: KLet, KIf, KAnd, KAndR, KOr, KOrR, KCond, KTrap, KHead, KArgs, KCallArgs,
     KApply. Applications (KHead, KArgs and KCallArgs with no arguments left, and KApply) are
     reduced to AppRel, the application relation, which is a hypothesis here: its proof is
     compat_app/compat_call's (JitKRefCompatClo). ObsT_swap moves between two frames with the same
     next move.
   - World reachability (world_closed): under SRel, the world's source locations are closed under
     the vector pointers in their cells, as are its target locations, both duplicate-free, of equal
     size (length w), allocated, and so at most each heap's length; related values point into the
     world, pointwise related (VRel_ptrs); world_closed_alloc is the same in JitEqBudgetStep's closed_in
     form. vptrs, closed_set, dptr and closed_alloc are JitEqBudgetWalk's data_ptrs and closed_in and
     JitEqBudgetStep's din and closed_in, same text; this file does not import those files, which would
     load JitKRef a second way. JitEqBudgetStep's S-local lok (lok_in) does NOT follow from SRel
     (SRel_lok_refuted).
   - sealed_stable and storehas_stable, by induction on star: under jit_rules no step changes a
     sealed name's function (sealed_step); defun_allowed refuses a sealed name, eval-kl's defun goes
     through the same eval_move_r rule, primitives never change gfuns (prim_gfuns), and port_prim is
     None (jit_port_prim_none).

   Does NOT prove: any compatibility lemma, the fundamental property, AppRel for any function value,
   fv against scoped (listed for this file in JitKRef.v's file map), or anything about the = budget. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefBase.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKRef.JitKRef
 JitKRefGround.JitKRefGround.

(* Locations of the vectors = can follow from a value (JitEqBudgetWalk.data_ptrs, same text). *)
Fixpoint vptrs (v : value) : list nat := match v with
 | VCons a b => vptrs a ++ vptrs b
 | VVec l => [l]
 | _ => [] end.

Definition nontrap (f : frame) : bool := match f with KTrap _ _ => false | _ => true end.

(* A literal, or a variable bound in rho: one silent step to its value. *)
Definition sval (rho : lenv) (e : expr) : option value := match e with
 | EVar x => lookup x rho | _ => lit_val e end.

Lemma wext_trans : forall w1 w2 w3, wext w1 w2 -> wext w2 w3 -> wext w1 w3.
Proof. intros w1 w2 w3 [I1 _] [I2 W]. split; [intros a A; apply I2, I1, A|exact W]. Qed.

Lemma same_id_incl : forall w w' r0 r, incl w w' -> same_id w r0 r -> same_id w' r0 r.
Proof.
 intros w w' r0 r I H. unfold same_id in *.
 destruct (closure_id r0), (closure_id r); auto.
Qed.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation runs := (JitKRef.JitKRef.runs sealed).
Notation StoreHas := (JitKRef.JitKRef.StoreHas D).
Notation ObsT := (JitKRef.JitKRef.ObsT sealed).
Notation SRel_with := (JitKRef.JitKRef.SRel_with D).
Notation KRel_with := (JitKRef.JitKRef.KRel_with sealed D).
Notation ERel_with := (JitKRef.JitKRef.ERel_with sealed D).
Notation VBody := (JitKRef.JitKRef.VBody sealed D).
Notation VRelF := (JitKRef.JitKRef.VRelF sealed D).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation KRel := (JitKRef.JitKRef.KRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation sealed_stable_statement := (JitKRef.JitKRef.sealed_stable_statement sealed).
Notation storehas_stable_statement := (JitKRef.JitKRef.storehas_stable_statement sealed D).
Notation VRel_down_statement := (JitKRef.JitKRef.VRel_down_statement sealed D).
Notation VRel_wext_statement := (JitKRef.JitKRef.VRel_wext_statement sealed D).
Notation ERel_down_statement := (JitKRef.JitKRef.ERel_down_statement sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation KRef_scope_statement := (JitKRef.JitKRef.KRef_scope_statement sealed D).
Notation VRelF_index := (JitKRefGround.JitKRefGround.VRelF_index sealed D).
Notation VRel_unfold := (JitKRefGround.JitKRefGround.VRel_unfold sealed D).

(* ======================= index and world structure ======================= *)
Lemma VBody_mono : forall V V' k j w v0 v, (j <= k)%nat -> (forall i, (i < j)%nat -> V i = V' i) ->
 VBody V k w v0 v -> VBody V' j w v0 v.
Proof.
 intros V V' k j w v0 v L Eq. revert v. induction v0 using value_rect'; intros v' H';
  destruct v'; try (cbn in H'; contradiction).
 11: { apply VBody_partial. apply VBody_partial in H' as [E F]. split; [exact E|].
   revert args0 F. induction H as [|x l Px Pl IH]; intros l1 F; inversion F; subst; constructor; auto. }
 all: cbn [JitKRef.JitKRef.VBody] in *; auto.
 - destruct H'; split; auto.
 - destruct H' as [Sid F]. split; [exact Sid|]. intros j' Lj w' Ww a0 a A.
   rewrite <- (Eq j' Lj) in A. eapply ERel_with_ext; [|apply F; [lia|exact Ww|exact A]].
   intros i Li. apply Eq. lia.
 - destruct H' as [Sid F]. split; [exact Sid|]. intros j' Lj w' Ww.
   eapply ERel_with_ext; [|apply F; [lia|exact Ww]]. intros i Li. apply Eq. lia.
Qed.

Lemma VBody_wext : forall V k w w' v0 v, wext w w' -> VBody V k w v0 v -> VBody V k w' v0 v.
Proof.
 intros V k w w' v0 v W. revert v. induction v0 using value_rect'; intros v' H';
  destruct v'; try (cbn in H'; contradiction).
 11: { apply VBody_partial. apply VBody_partial in H' as [E F]. split; [exact E|].
   revert args0 F. induction H as [|x l Px Pl IH]; intros l1 F; inversion F; subst; constructor; auto. }
 all: cbn [JitKRef.JitKRef.VBody] in *; auto.
 - destruct H'; split; auto.
 - apply (proj1 W). exact H'.
 - destruct H' as [Sid F]. split; [eapply same_id_incl; [apply W|exact Sid]|].
   intros j' Lj w'' W2 a0 a A. apply F; [exact Lj|eapply wext_trans; eauto|exact A].
 - destruct H' as [Sid F]. split; [eapply same_id_incl; [apply W|exact Sid]|].
   intros j' Lj w'' W2. apply F; [exact Lj|eapply wext_trans; eauto].
Qed.

Theorem VRel_down : VRel_down_statement.
Proof.
 intros k j w v0 v L H. rewrite (VRel_unfold k) in H. rewrite (VRel_unfold j).
 eapply VBody_mono; [exact L| |exact H].
 intros i Li. destruct k as [|k]; [lia|]. destruct j as [|j]; [lia|]. cbv beta iota.
 rewrite !VRelF_index by lia. reflexivity.
Qed.

Theorem VRel_wext : VRel_wext_statement.
Proof.
 intros k w w' v0 v W H. rewrite (VRel_unfold k) in H |- *. eapply VBody_wext; eauto.
Qed.

Lemma VRelF_agree : forall k j i, (j <= k)%nat -> (i <= j)%nat -> VRelF k i = VRelF j i.
Proof. intros k j i L1 L2. rewrite !VRelF_index by lia. reflexivity. Qed.

Lemma KRel_with_norm : forall k j w K0 K, (j <= k)%nat -> KRel_with (VRelF k) j w K0 K <-> KRel j w K0 K.
Proof.
 intros k j w K0 K L. unfold JitKRef.JitKRef.KRel. split; apply KRel_with_ext; intros i Li.
 - apply VRelF_agree; lia.
 - symmetry. apply VRelF_agree; lia.
Qed.

(* KRel and ERel with every index family read as VRel, SRel and KRel. *)
Lemma KRel_iff : forall k w K0 K, KRel k w K0 K <-> forall j, (j <= k)%nat -> forall w', wext w w' ->
 (forall v0 v s0 s, VRel j w' v0 v -> SRel j w' s0 s -> ObsT j w' (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s)) /\
 (forall x s0 s, SRel j w' s0 s -> ObsT j w' (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s)).
Proof.
 intros k w K0 K. unfold JitKRef.JitKRef.KRel, JitKRef.JitKRef.SRel. split; intros H j L w' W;
  specialize (H j L w' W); rewrite (VRelF_index k j L) in *; exact H.
Qed.

Lemma ERel_iff : forall k w r0 e0 r e, ERel k w r0 e0 r e <-> forall j, (j <= k)%nat -> forall w', wext w w' ->
 forall K0 K, KRel j w' K0 K -> forall s0 s, SRel j w' s0 s -> ObsT j w' (Cfg (Eval r0 e0) K0 s0) (Cfg (Eval r e) K s).
Proof.
 intros k w r0 e0 r e. unfold JitKRef.JitKRef.ERel, JitKRef.JitKRef.SRel. split; intros H j L w' W K0 K HK s0 s HS.
 - apply (H j L w' W); [apply KRel_with_norm; assumption|rewrite (VRelF_index k j L); exact HS].
 - apply (H j L w' W); [apply (KRel_with_norm k); assumption|rewrite <- (VRelF_index k j L); exact HS].
Qed.

Theorem ERel_down : ERel_down_statement.
Proof.
 intros k j w r0 e0 r e L H. apply ERel_iff. intros j' L' w' W K0 K HK s0 s HS.
 apply (proj1 (ERel_iff k w r0 e0 r e) H j' ltac:(lia) w' W K0 K HK s0 s HS).
Qed.

Theorem ERel_wext : forall k w w' r0 e0 r e, wext w w' -> ERel k w r0 e0 r e -> ERel k w' r0 e0 r e.
Proof.
 intros k w w' r0 e0 r e W H. apply ERel_iff. intros j L w'' W2 K0 K HK s0 s HS.
 apply (proj1 (ERel_iff k w r0 e0 r e) H j L w'' (wext_trans _ _ _ W W2) K0 K HK s0 s HS).
Qed.

Theorem KRel_down : forall k j w K0 K, (j <= k)%nat -> KRel k w K0 K -> KRel j w K0 K.
Proof.
 intros k j w K0 K L H. apply KRel_iff. intros j' L' w' W. apply (proj1 (KRel_iff k w K0 K) H); [lia|exact W].
Qed.

Theorem KRel_wext : forall k w w' K0 K, wext w w' -> KRel k w K0 K -> KRel k w' K0 K.
Proof.
 intros k w w' K0 K W H. apply KRel_iff. intros j L w'' W2.
 apply (proj1 (KRel_iff k w K0 K) H); [exact L|eapply wext_trans; eauto].
Qed.

Theorem KRel_mono : forall k j w w' K0 K, (j <= k)%nat -> wext w w' -> KRel k w K0 K -> KRel j w' K0 K.
Proof. intros. eapply KRel_down; [eassumption|]. eapply KRel_wext; eassumption. Qed.

Theorem ERel_mono : forall k j w w' r0 e0 r e, (j <= k)%nat -> wext w w' -> ERel k w r0 e0 r e -> ERel j w' r0 e0 r e.
Proof. intros. eapply ERel_down; [eassumption|]. eapply ERel_wext; eassumption. Qed.

Theorem VRel_mono : forall k j w w' v0 v, (j <= k)%nat -> wext w w' -> VRel k w v0 v -> VRel j w' v0 v.
Proof. intros. eapply VRel_down; [eassumption|]. eapply VRel_wext; eassumption. Qed.

Lemma Forall2_VRel_mono : forall k j w w' l0 l, (j <= k)%nat -> wext w w' ->
 Forall2 (VRel k w) l0 l -> Forall2 (VRel j w') l0 l.
Proof. intros k j w w' l0 l L W F. eapply Forall2_impl; [|exact F]. intros a b; apply VRel_mono; assumption. Qed.

Lemma SRel_wf : forall k w s0 s, SRel k w s0 s -> wf_world w.
Proof. intros k w s0 s H; apply H. Qed.

Theorem SRel_down : forall k j w s0 s, (j <= k)%nat -> SRel k w s0 s -> SRel j w s0 s.
Proof.
 intros k j w s0 s L (W & H0 & H1 & G & Gv & Hp).
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact G|split]]]].
 - eapply Forall2_impl; [|exact Gv]. intros [x a] [y b] [E A]; split; [exact E|]. eapply VRel_down; eauto.
 - intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. repeat split; auto.
   eapply Forall2_impl; [|exact F]. intros a b; apply VRel_down; exact L.
Qed.

(* SRel is NOT monotone up in wext (SRel_wext_refuted, below): a pair the larger world adds
   needs its cells, related. This is the true form. *)
Theorem SRel_wext_cells : forall k w w' s0 s, SRel k w s0 s -> wext w w' ->
 (forall l0 l, In (l0, l) w' -> In (l0, l) w \/ exists c0 c, nth_error (heap s0) l0 = Some c0 /\
    nth_error (heap s) l = Some c /\ Forall2 (VRel k w') c0 c) ->
 SRel k w' s0 s.
Proof.
 intros k w w' s0 s (W & H0 & H1 & G & Gv & Hp) Wx New.
 split; [apply Wx|split; [exact H0|split; [exact H1|split; [exact G|split]]]].
 - eapply Forall2_impl; [|exact Gv]. intros [x a] [y b] [E A]; split; [exact E|]. eapply VRel_wext; eauto.
 - intros l0 l I. destruct (New _ _ I) as [Iw|Hc]; [|exact Hc].
   destruct (Hp _ _ Iw) as (c0 & c & N0 & N & F). exists c0, c. repeat split; auto.
   eapply Forall2_impl; [|exact F]. intros a b; apply VRel_wext; exact Wx.
Qed.

Theorem EnvRel_mono : forall k j w w' g r0 r, (j <= k)%nat -> wext w w' ->
 EnvRel_with (VRel k) w g r0 r -> EnvRel_with (VRel j) w' g r0 r.
Proof.
 intros k j w w' g r0 r L W H x I. destruct (H x I) as (v0 & v & E0 & E & V).
 exists v0, v. repeat split; auto. eapply VRel_mono; eauto.
Qed.

(* KRef relates on its scope only, so a larger scope asks more of the environments. *)
Theorem KRef_scope : KRef_scope_statement.
Proof.
 intros g g' e0 e I H k w rho0 rho W HE. apply H; [exact W|]. intros x Ix. apply HE. apply I. exact Ix.
Qed.

Theorem ObsT_down : forall k j w c0 c, (j <= k)%nat -> ObsT k w c0 c -> ObsT j w c0 c.
Proof. intros k j w c0 c L H n t c' Ln Hr. apply (H n t c'); [lia|exact Hr]. Qed.

(* ObsT is antitone in the world: a smaller world asks less of the matching source run. *)
Theorem ObsT_wext_anti : forall k w w' c0 c, wext w w' -> ObsT k w' c0 c -> ObsT k w c0 c.
Proof.
 intros k w w' c0 c W H n t c' L Hr. destruct (H n t c' L Hr) as (A & B & C). split; [|split; [|exact C]].
 - intros v s E. destruct (A v s E) as (v0 & s0 & w'' & S0 & W2 & G1 & G2).
   exists v0, s0, w''. split; [exact S0|split; [eapply wext_trans; eauto|split; assumption]].
 - intros x s E. destruct (B x s E) as (s0 & w'' & S0 & W2 & G2).
   exists s0, w''. split; [exact S0|split; [eapply wext_trans; eauto|assumption]].
Qed.

Lemma ObsT_0 : forall w c0 c, ObsT 0 w c0 c.
Proof. intros w c0 c n t c' L. lia. Qed.

(* ======================= observation: anti-reduction and target steps ======================= *)
(* ObsT with a source trace prefix t1: the matching source run performs t1 first. *)
Definition ObsTr (k : nat) (w : world) (t1 : trace) (c0 c : config) : Prop :=
 forall n t c', (n < k)%nat -> runs n c t c' ->
  (forall v s, c' = Cfg (Ret v) [] s -> exists v0 s0 w',
     srun c0 (t1 ++ t) (Cfg (Ret v0) [] s0) /\ wext w w' /\ GVal w' v0 v /\ GStore w' s0 s) /\
  (forall x s, c' = Cfg (Throw x) [] s -> exists s0 w',
     srun c0 (t1 ++ t) (Cfg (Throw x) [] s0) /\ wext w w' /\ GStore w' s0 s) /\
  (forall why, next_r R P c' = MWrong why -> exists c0' why0,
     srun c0 (t1 ++ t) c0' /\ next_r R P c0' = MWrong why0).

Lemma ObsT_ObsTr : forall k w c0 c, ObsT k w c0 c <-> ObsTr k w [] c0 c.
Proof. intros k w c0 c. split; intro H; exact H. Qed.

Lemma srun_trans : forall c1 t1 c2 t2 c3, srun c1 t1 c2 -> srun c2 t2 c3 -> srun c1 (t1 ++ t2) c3.
Proof. intros. eapply star_trans; eassumption. Qed.

Lemma srun_tau : forall c c' t c'', next_r R P c = MTau c' -> srun c' t c'' -> srun c t c''.
Proof.
 intros c c' t c'' E H. change t with (trace_of Tau ++ t). econstructor; [|exact H]. apply step_r_tau; exact E.
Qed.

Lemma srun_res : forall c x r t c'', running_state c = true -> resource_exn R r = Some x ->
 srun (Cfg (Throw x) (kont c) (mem c)) t c'' -> srun c t c''.
Proof.
 intros c x r t c'' Rs Rx H. change t with (trace_of Tau ++ t). econstructor; [|exact H].
 eapply step_r_resource; eassumption.
Qed.

Lemma srun_refl : forall c, srun c [] c.
Proof. intro c. constructor. Qed.

(* Source anti-reduction: a source prefix of any trace. *)
Lemma ObsTr_anti : forall k w t1 t2 c0 c0' c, srun c0 t1 c0' -> ObsTr k w t2 c0' c -> ObsTr k w (t1 ++ t2) c0 c.
Proof.
 intros k w t1 t2 c0 c0' c S0 H n t c' L Hr. destruct (H n t c' L Hr) as (A & B & C).
 split; [|split].
 - intros v s E. destruct (A v s E) as (v0 & s0 & w' & S1 & X). exists v0, s0, w'.
   split; [|exact X]. rewrite <- app_assoc. eapply srun_trans; eauto.
 - intros x s E. destruct (B x s E) as (s0 & w' & S1 & X). exists s0, w'.
   split; [|exact X]. rewrite <- app_assoc. eapply srun_trans; eauto.
 - intros why E. destruct (C why E) as (c1 & why0 & S1 & X). exists c1, why0.
   split; [|exact X]. rewrite <- app_assoc. eapply srun_trans; eauto.
Qed.

Theorem ObsT_anti : forall k w c0 c0' c, srun c0 [] c0' -> ObsT k w c0' c -> ObsT k w c0 c.
Proof. intros k w c0 c0' c S0 H. apply ObsT_ObsTr. exact (ObsTr_anti k w [] [] c0 c0' c S0 H). Qed.

(* The IO form: a source run with trace t1 followed by ObsT gives ObsT with t1 prepended. *)
Theorem ObsT_anti_io : forall k w t1 c0 c0' c, srun c0 t1 c0' -> ObsT k w c0' c -> ObsTr k w t1 c0 c.
Proof.
 intros k w t1 c0 c0' c S0 H. rewrite <- (app_nil_r t1). exact (ObsTr_anti k w t1 [] c0 c0' c S0 H).
Qed.

(* A configuration from which the target can move: not a final state, not wrong. *)
Definition nonterm (c : config) : Prop :=
 match next_r R P c with MTau _ | MIO _ _ => True | _ => False end.

(* Target-step reduction: if every step of the target, with its label, is matched by the source
   with that label's trace, at one index less, then the configurations are related. *)
Theorem ObsT_step : forall k w c0 c, nonterm c ->
 (forall l c1, step_r R P c l c1 -> ObsTr k w (trace_of l) c0 c1) -> ObsT (S k) w c0 c.
Proof.
 intros k w c0 c Nt H n t c' L Hr. inversion Hr as [c2|n' c2 l c1 t' c3 St Hr']; subst.
 - split; [|split].
   + intros v s E; subst. unfold nonterm in Nt. cbn in Nt. contradiction.
   + intros x s E; subst. unfold nonterm in Nt. cbn in Nt. contradiction.
   + intros why E. unfold nonterm in Nt. rewrite E in Nt. contradiction.
 - exact (H l c1 St n' t' c' ltac:(lia) Hr').
Qed.

(* Forward: one target step out of a related pair, with its trace as the source prefix. *)
Lemma ObsT_fwd : forall k w c0 c l c1, ObsT (S k) w c0 c -> step_r R P c l c1 -> ObsTr k w (trace_of l) c0 c1.
Proof.
 intros k w c0 c l c1 H St n t c' L Hr. apply (H (S n) (trace_of l ++ t) c'); [lia|econstructor; eauto].
Qed.

Lemma step_r_cases : forall c l c1, step_r R P c l c1 ->
 (next_r R P c = MTau c1 /\ l = Tau) \/
 (exists q kk r, next_r R P c = MIO q kk /\ l = Obs (EvIO q r) /\ c1 = kk r) \/
 (exists r x, running_state c = true /\ resource_exn R r = Some x /\ l = Tau /\ c1 = Cfg (Throw x) (kont c) (mem c)).
Proof.
 intros c l c1 H. destruct H as [c c' E|c q kk r E|c r x Rs Rx].
 - left; auto.
 - right; left; exists q, kk, r; auto.
 - right; right; exists r, x; auto.
Qed.

(* The running-state form: a target resource step is matched by the source's own resource step
   to the same exception, so the hypotheses are the Throw configurations (which KRel's Throw
   clause gives) and the target's own moves. *)
Theorem ObsT_running : forall k w c0 c, running_state c0 = true -> nonterm c ->
 (forall x, ObsT k w (Cfg (Throw x) (kont c0) (mem c0)) (Cfg (Throw x) (kont c) (mem c))) ->
 (forall c1, next_r R P c = MTau c1 -> exists c0', srun c0 [] c0' /\ ObsT k w c0' c1) ->
 (forall q kk r, next_r R P c = MIO q kk -> exists c0', srun c0 [EvIO q r] c0' /\ ObsT k w c0' (kk r)) ->
 ObsT (S k) w c0 c.
Proof.
 intros k w c0 c Rs Nt Hx Ht Hio. apply ObsT_step; [exact Nt|]. intros l c1 St.
 destruct (step_r_cases _ _ _ St) as [[E ->]|[(q & kk & r & E & -> & ->)|(r & x & Rc & Rx & -> & ->)]].
 - destruct (Ht c1 E) as (c0' & S0 & O). exact (ObsT_anti_io _ _ [] _ _ _ S0 O).
 - destruct (Hio q kk r E) as (c0' & S0 & O). exact (ObsT_anti_io _ _ [EvIO q r] _ _ _ S0 O).
 - apply (ObsT_anti_io _ _ [] _ (Cfg (Throw x) (kont c0) (mem c0))); [|apply Hx].
   eapply srun_res; [exact Rs|exact Rx|apply srun_refl].
Qed.

Lemma KRel_throw : forall k w K0 K x s0 s, KRel k w K0 K -> SRel k w s0 s ->
 ObsT k w (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s).
Proof.
 intros k w K0 K x s0 s H HS. apply (proj1 (KRel_iff k w K0 K) H k (le_n k) w); [|exact HS].
 apply wext_refl. eapply SRel_wf; eauto.
Qed.

Lemma KRel_ret : forall k w K0 K v0 v s0 s, KRel k w K0 K -> VRel k w v0 v -> SRel k w s0 s ->
 ObsT k w (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s).
Proof.
 intros k w K0 K v0 v s0 s H HV HS. apply (proj1 (KRel_iff k w K0 K) H k (le_n k) w); [|exact HV|exact HS].
 apply wext_refl. eapply SRel_wf; eauto.
Qed.

(* step_r_resource matching: a target resource error from a running state with continuation K is
   matched by the source's resource error from its running state, then KRel's Throw clause. *)
Theorem resource_match : forall k w ctl0 K0 K s0 s r x, running_state (Cfg ctl0 K0 s0) = true ->
 resource_exn R r = Some x -> KRel k w K0 K -> SRel k w s0 s ->
 exists c0', srun (Cfg ctl0 K0 s0) [] c0' /\ ObsT k w c0' (Cfg (Throw x) K s).
Proof.
 intros k w ctl0 K0 K s0 s r x Rs Rx HK HS. exists (Cfg (Throw x) K0 s0). split.
 - eapply (srun_res (Cfg ctl0 K0 s0)); [exact Rs|exact Rx|apply srun_refl].
 - apply KRel_throw; assumption.
Qed.

(* Wrong-state matching: a target in a wrong state has no step, so a source that can reach a
   wrong state silently matches it. *)
Theorem wrong_match : forall k w c0 c why, ctl c = Wrong why ->
 (exists c0' why0, srun c0 [] c0' /\ next_r R P c0' = MWrong why0) -> ObsT k w c0 c.
Proof.
 intros k w c0 [ctl0 K s] why E Hw n t c' L Hr. cbn in E. subst ctl0.
 inversion Hr as [c2|n' c2 l c1 t' c3 St Hr']; subst.
 - split; [|split].
   + intros v s' E; discriminate.
   + intros x s' E; discriminate.
   + intros why' _. exact Hw.
 - exfalso. destruct (step_r_cases _ _ _ St) as [[E _]|[(q & kk & r & E & _)|(r & x & Rc & _)]];
    cbn in *; discriminate.
Qed.

(* ======================= helpers at one index less ======================= *)
Lemma ERel_apply : forall k j w w' r0 e0 r e K0 K s0 s, ERel k w r0 e0 r e -> (j <= k)%nat -> wext w w' ->
 KRel j w' K0 K -> SRel j w' s0 s -> ObsT j w' (Cfg (Eval r0 e0) K0 s0) (Cfg (Eval r e) K s).
Proof. intros k j w w' r0 e0 r e K0 K s0 s He L W HK HS. exact (proj1 (ERel_iff k w r0 e0 r e) He j L w' W K0 K HK s0 s HS). Qed.

Lemma ERel_at : forall k j w w' r0 e0 r e K0 K s0 s, (S j <= k)%nat -> wext w w' -> ERel k w r0 e0 r e ->
 KRel k w K0 K -> SRel (S j) w' s0 s -> ObsT j w' (Cfg (Eval r0 e0) K0 s0) (Cfg (Eval r e) K s).
Proof.
 intros k j w w' r0 e0 r e K0 K s0 s L W He HK HS. eapply ERel_apply; [exact He|lia|exact W| |].
 - eapply KRel_mono; [|exact W|exact HK]; lia.
 - eapply SRel_down; [|exact HS]; lia.
Qed.

Lemma throw_at : forall k j w w' K0 K x s0 s, (S j <= k)%nat -> wext w w' -> KRel k w K0 K -> SRel (S j) w' s0 s ->
 ObsT j w' (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s).
Proof.
 intros k j w w' K0 K x s0 s L W HK HS. apply KRel_throw; [eapply KRel_mono; [|exact W|exact HK]; lia|].
 eapply SRel_down; [|exact HS]; lia.
Qed.

Lemma ret_at : forall k j w w' K0 K v0 v s0 s, (S j <= k)%nat -> wext w w' -> KRel k w K0 K ->
 VRel (S j) w' v0 v -> SRel (S j) w' s0 s -> ObsT j w' (Cfg (Ret v0) K0 s0) (Cfg (Ret v) K s).
Proof.
 intros k j w w' K0 K v0 v s0 s L W HK HV HS. apply KRel_ret; [eapply KRel_mono; [|exact W|exact HK]; lia| |].
 - eapply VRel_down; [|exact HV]; lia.
 - eapply SRel_down; [|exact HS]; lia.
Qed.

Lemma wext_self : forall k w s0 s, SRel k w s0 s -> wext w w.
Proof. intros k w s0 s HS. apply wext_refl. eapply SRel_wf; eauto. Qed.

Lemma Forall2_ERel_mono : forall k j w w' r0 r l0 l, (j <= k)%nat -> wext w w' ->
 Forall2 (fun a0 a => ERel k w r0 a0 r a) l0 l -> Forall2 (fun a0 a => ERel j w' r0 a0 r a) l0 l.
Proof. intros k j w w' r0 r l0 l L W F. eapply Forall2_impl; [|exact F]. intros a0 a; apply ERel_mono; assumption. Qed.

(* ======================= the bind lemma: a step that pushes a frame ======================= *)
(* The first step of a compound form: source and target each move silently to a subexpression
   under a continuation built from their own (F0 K0 and F K). If the built continuations are
   related whenever the given ones are, and the subexpressions are related, at every index below
   k, the forms are related at k. A target resource step is matched by the source's. *)
Theorem ERel_push : forall k w rho0 e0 rho e rho0' e0' rho' e' (F0 F : list frame -> list frame),
 (forall K0 s0, next_r R P (Cfg (Eval rho0 e0) K0 s0) = MTau (Cfg (Eval rho0' e0') (F0 K0) s0)) ->
 (forall K s, next_r R P (Cfg (Eval rho e) K s) = MTau (Cfg (Eval rho' e') (F K) s)) ->
 (forall j w' K0 K, (j < k)%nat -> wext w w' -> KRel j w' K0 K -> KRel j w' (F0 K0) (F K)) ->
 (forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0' e0' rho' e') ->
 ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e rho0' e0' rho' e' F0 F E0 E HF He. apply ERel_iff.
 intros j L w' W K0 K HK s0 s HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_running.
 - reflexivity.
 - unfold nonterm. rewrite E. exact I.
 - intros x. cbn [kont mem]. apply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite E in E1. injection E1 as <-. eexists; split; [eapply srun_tau; [apply E0|apply srun_refl]|].
   eapply ERel_apply; [apply (He j w'); [lia|exact W]|apply le_n|eapply wext_self; exact HS| |].
   + apply HF; [lia|exact W|eapply KRel_down; [|exact HK]; lia].
   + eapply SRel_down; [|exact HS]; lia.
 - intros q kk r E1. rewrite E in E1. discriminate.
Qed.

Lemma push_jit : forall f K c s, push P f K c s = Cfg c (f :: K) s.
Proof. reflexivity. Qed.

(* ======================= frames ======================= *)
Lemma throw_frame_next : forall f x K s, nontrap f = true -> next_r R P (Cfg (Throw x) (f :: K) s) = MTau (Cfg (Throw x) K s).
Proof. intros f x K s N. destruct f; try discriminate; reflexivity. Qed.

Lemma ObsT_throw_frame : forall k w f0 f x K0 K s0 s, nontrap f0 = true -> nontrap f = true ->
 ObsT k w (Cfg (Throw x) K0 s0) (Cfg (Throw x) K s) -> ObsT (S k) w (Cfg (Throw x) (f0 :: K0) s0) (Cfg (Throw x) (f :: K) s).
Proof.
 intros k w f0 f x K0 K s0 s N0 N H. apply ObsT_step.
 - unfold nonterm. rewrite throw_frame_next by exact N. exact I.
 - intros l c1 St. destruct (step_r_cases _ _ _ St) as [[E ->]|[(q & kk & r & E & _)|(r & y & Rc & _)]].
   + rewrite throw_frame_next in E by exact N. injection E as <-.
     apply (ObsT_anti_io _ _ [] _ (Cfg (Throw x) K0 s0)); [|exact H].
     eapply srun_tau; [apply throw_frame_next; exact N0|apply srun_refl].
   + rewrite throw_frame_next in E by exact N. discriminate.
   + cbn in Rc. discriminate.
Qed.

(* The Throw clause of every non-trap frame, from the Throw clause of the rest. *)
Theorem KRel_throw_frame : forall k w f0 f K0 K, KRel k w K0 K -> nontrap f0 = true -> nontrap f = true ->
 forall j w' x s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s ->
 ObsT j w' (Cfg (Throw x) (f0 :: K0) s0) (Cfg (Throw x) (f :: K) s).
Proof.
 intros k w f0 f K0 K HK N0 N j w' x s0 s L W HS. destruct j as [|j]; [apply ObsT_0|].
 apply ObsT_throw_frame; [exact N0|exact N|]. eapply throw_at; eauto.
Qed.

Theorem KRel_push : forall k w f0 f K0 K, KRel k w K0 K -> nontrap f0 = true -> nontrap f = true ->
 (forall j w' v0 v s0 s, (j <= k)%nat -> wext w w' -> VRel j w' v0 v -> SRel j w' s0 s ->
   ObsT j w' (Cfg (Ret v0) (f0 :: K0) s0) (Cfg (Ret v) (f :: K) s)) ->
 KRel k w (f0 :: K0) (f :: K).
Proof.
 intros k w f0 f K0 K HK N0 N Hr. apply KRel_iff. intros j L w' W. split.
 - intros v0 v s0 s HV HS. apply Hr; assumption.
 - intros x s0 s HS. eapply KRel_throw_frame; eauto.
Qed.

(* The Ret clause of a frame whose return is always a silent step. *)
Lemma ret_frame_tau : forall k w f0 f K0 K, KRel k w K0 K -> nontrap f0 = true -> nontrap f = true ->
 (forall j w' v0 v s0 s c1, (S j <= k)%nat -> wext w w' -> VRel (S j) w' v0 v -> SRel (S j) w' s0 s ->
   next_r R P (Cfg (Ret v) (f :: K) s) = MTau c1 ->
   exists c0', srun (Cfg (Ret v0) (f0 :: K0) s0) [] c0' /\ ObsT j w' c0' c1) ->
 (forall v s, exists c1, next_r R P (Cfg (Ret v) (f :: K) s) = MTau c1) ->
 KRel k w (f0 :: K0) (f :: K).
Proof.
 intros k w f0 f K0 K HK N0 N Ht Hm. apply KRel_push; [exact HK|exact N0|exact N|].
 intros j w' v0 v s0 s L W HV HS. destruct j as [|j]; [apply ObsT_0|].
 destruct (Hm v s) as [c1 E]. apply ObsT_running.
 - reflexivity.
 - unfold nonterm. rewrite E. exact I.
 - intros x. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|exact N0|exact N|lia|exact W|].
   eapply SRel_down; [|exact HS]; lia.
 - intros c2 E2. rewrite E in E2. injection E2 as <-. eapply Ht; eauto.
 - intros q kk r E2. rewrite E in E2. discriminate.
Qed.

Definition asbool (v : value) : option bool := match v with VBool b => Some b | _ => None end.

Lemma VRel_asbool : forall k w v0 v, VRel k w v0 v -> asbool v0 = asbool v.
Proof.
 intros k w v0 v H. rewrite (VRel_unfold k) in H.
 destruct v0, v; cbn [JitKRef.JitKRef.VBody] in H; try contradiction; cbn; congruence.
Qed.

Lemma VRel_bool : forall k w b, VRel k w (VBool b) (VBool b).
Proof. intros k w b. rewrite (VRel_unfold k). reflexivity. Qed.

Lemma next_KLet : forall v x b rho K s, next_r R P (Cfg (Ret v) (KLet x b rho :: K) s) = MTau (Cfg (Eval ((x, v) :: rho) b) K s).
Proof. reflexivity. Qed.
Lemma next_KIf : forall v a b rho K s, next_r R P (Cfg (Ret v) (KIf a b rho :: K) s) =
 MTau (Cfg (match asbool v with Some true => Eval rho a | Some false => Eval rho b | None => Throw XNotBoolean end) K s).
Proof. intros v; destruct v as [| |[|]| | | | | | | | |]; reflexivity. Qed.
Lemma next_KCond : forall v b rest rho K s, next_r R P (Cfg (Ret v) (KCond b rest rho :: K) s) =
 MTau (Cfg (match asbool v with Some true => Eval rho b | Some false => Eval rho (ECond rest) | None => Throw XNotBoolean end) K s).
Proof. intros v; destruct v as [| |[|]| | | | | | | | |]; reflexivity. Qed.
Lemma next_KAnd : forall v b rho K s, next_r R P (Cfg (Ret v) (KAnd b rho :: K) s) =
 match asbool v with Some true => MTau (Cfg (Eval rho b) (KAndR :: K) s) | Some false => MTau (Cfg (Ret (VBool false)) K s)
 | None => MTau (Cfg (Throw XNotBoolean) K s) end.
Proof. intros v; destruct v as [| |[|]| | | | | | | | |]; reflexivity. Qed.
Lemma next_KOr : forall v b rho K s, next_r R P (Cfg (Ret v) (KOr b rho :: K) s) =
 match asbool v with Some true => MTau (Cfg (Ret (VBool true)) K s) | Some false => MTau (Cfg (Eval rho b) (KOrR :: K) s)
 | None => MTau (Cfg (Throw XNotBoolean) K s) end.
Proof. intros v; destruct v as [| |[|]| | | | | | | | |]; reflexivity. Qed.
Lemma next_KAndR : forall v K s, next_r R P (Cfg (Ret v) (KAndR :: K) s) =
 MTau (Cfg (match asbool v with Some b => Ret (VBool b) | None => Throw XNotBoolean end) K s).
Proof. intros v; destruct v; reflexivity. Qed.
Lemma next_KOrR : forall v K s, next_r R P (Cfg (Ret v) (KOrR :: K) s) =
 MTau (Cfg (match asbool v with Some b => Ret (VBool b) | None => Throw XNotBoolean end) K s).
Proof. intros v; destruct v; reflexivity. Qed.

Theorem KRel_KLet : forall k w x0 b0 rho0 x b rho K0 K, KRel k w K0 K ->
 (forall j w' v0 v, (j <= k)%nat -> wext w w' -> VRel j w' v0 v -> ERel j w' ((x0, v0) :: rho0) b0 ((x, v) :: rho) b) ->
 KRel k w (KLet x0 b0 rho0 :: K0) (KLet x b rho :: K).
Proof.
 intros k w x0 b0 rho0 x b rho K0 K HK Hb. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KLet in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KLet|apply srun_refl]|].
   eapply (ERel_at (S j)); [apply le_n|eapply wext_self; exact HS|apply Hb; [exact L|exact W|exact HV]| |exact HS].
   eapply KRel_mono; [exact L|exact W|exact HK].
 - intros v s. eexists. apply next_KLet.
Qed.

Theorem KRel_KIf : forall k w a0 b0 rho0 a b rho K0 K, KRel k w K0 K ->
 ERel k w rho0 a0 rho a -> ERel k w rho0 b0 rho b -> KRel k w (KIf a0 b0 rho0 :: K0) (KIf a b rho :: K).
Proof.
 intros k w a0 b0 rho0 a b rho K0 K HK Ha Hb. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KIf in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KIf|apply srun_refl]|].
   rewrite (VRel_asbool _ _ _ _ HV). destruct (asbool v) as [[|]|].
   + eapply ERel_at; eauto.
   + eapply ERel_at; eauto.
   + eapply throw_at; eauto.
 - intros v s. eexists. apply next_KIf.
Qed.

Theorem KRel_KCond : forall k w b0 rest0 rho0 b rest rho K0 K, KRel k w K0 K ->
 ERel k w rho0 b0 rho b -> ERel k w rho0 (ECond rest0) rho (ECond rest) ->
 KRel k w (KCond b0 rest0 rho0 :: K0) (KCond b rest rho :: K).
Proof.
 intros k w b0 rest0 rho0 b rest rho K0 K HK Hb Hr. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KCond in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KCond|apply srun_refl]|].
   rewrite (VRel_asbool _ _ _ _ HV). destruct (asbool v) as [[|]|].
   + eapply ERel_at; eauto.
   + eapply ERel_at; eauto.
   + eapply throw_at; eauto.
 - intros v s. eexists. apply next_KCond.
Qed.

Theorem KRel_KAndR : forall k w K0 K, KRel k w K0 K -> KRel k w (KAndR :: K0) (KAndR :: K).
Proof.
 intros k w K0 K HK. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KAndR in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KAndR|apply srun_refl]|].
   rewrite (VRel_asbool _ _ _ _ HV). destruct (asbool v) as [b|].
   + eapply ret_at; eauto. apply VRel_bool.
   + eapply throw_at; eauto.
 - intros v s. eexists. apply next_KAndR.
Qed.

Theorem KRel_KOrR : forall k w K0 K, KRel k w K0 K -> KRel k w (KOrR :: K0) (KOrR :: K).
Proof.
 intros k w K0 K HK. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KOrR in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KOrR|apply srun_refl]|].
   rewrite (VRel_asbool _ _ _ _ HV). destruct (asbool v) as [b|].
   + eapply ret_at; eauto. apply VRel_bool.
   + eapply throw_at; eauto.
 - intros v s. eexists. apply next_KOrR.
Qed.

Theorem KRel_KAnd : forall k w b0 rho0 b rho K0 K, KRel k w K0 K -> ERel k w rho0 b0 rho b ->
 KRel k w (KAnd b0 rho0 :: K0) (KAnd b rho :: K).
Proof.
 intros k w b0 rho0 b rho K0 K HK Hb. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. pose proof (next_KAnd v0 b0 rho0 K0 s0) as E0.
   rewrite next_KAnd in E. rewrite (VRel_asbool _ _ _ _ HV) in E0.
   destruct (asbool v) as [[|]|]; injection E as <-; (eexists; split; [eapply srun_tau; [exact E0|apply srun_refl]|]).
   + eapply ERel_at; eauto. apply KRel_KAndR; exact HK.
   + eapply ret_at; eauto. apply VRel_bool.
   + eapply throw_at; eauto.
 - intros v s. rewrite next_KAnd. destruct (asbool v) as [[|]|]; eexists; reflexivity.
Qed.

Theorem KRel_KOr : forall k w b0 rho0 b rho K0 K, KRel k w K0 K -> ERel k w rho0 b0 rho b ->
 KRel k w (KOr b0 rho0 :: K0) (KOr b rho :: K).
Proof.
 intros k w b0 rho0 b rho K0 K HK Hb. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. pose proof (next_KOr v0 b0 rho0 K0 s0) as E0.
   rewrite next_KOr in E. rewrite (VRel_asbool _ _ _ _ HV) in E0.
   destruct (asbool v) as [[|]|]; injection E as <-; (eexists; split; [eapply srun_tau; [exact E0|apply srun_refl]|]).
   + eapply ret_at; eauto. apply VRel_bool.
   + eapply ERel_at; eauto. apply KRel_KOrR; exact HK.
   + eapply throw_at; eauto.
 - intros v s. rewrite next_KOr. destruct (asbool v) as [[|]|]; eexists; reflexivity.
Qed.

Lemma next_KTrap_ret : forall v h rho K s, next_r R P (Cfg (Ret v) (KTrap h rho :: K) s) = MTau (Cfg (Ret v) K s).
Proof. reflexivity. Qed.
Lemma next_KTrap_throw : forall x h rho K s,
 next_r R P (Cfg (Throw x) (KTrap h rho :: K) s) = MTau (Cfg (Eval rho h) (KApply [VExn x] :: K) s).
Proof. reflexivity. Qed.

(* The trap frame: values pass through; an exception runs the handler and applies it. *)
Theorem KRel_KTrap : forall k w h0 rho0 h rho K0 K, KRel k w K0 K -> ERel k w rho0 h0 rho h ->
 (forall x, KRel k w (KApply [VExn x] :: K0) (KApply [VExn x] :: K)) ->
 KRel k w (KTrap h0 rho0 :: K0) (KTrap h rho :: K).
Proof.
 intros k w h0 rho0 h rho K0 K HK Hh Hx.
 assert (Th : forall j w' x s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s ->
   ObsT j w' (Cfg (Throw x) (KTrap h0 rho0 :: K0) s0) (Cfg (Throw x) (KTrap h rho :: K) s)).
 { intros j w' x s0 s L W HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_step.
   - unfold nonterm. rewrite next_KTrap_throw. exact I.
   - intros l c1 St. destruct (step_r_cases _ _ _ St) as [[E ->]|[(q & kk & r & E & _)|(r & y & Rc & _)]].
     + rewrite next_KTrap_throw in E. injection E as <-.
       apply (ObsT_anti_io _ _ [] _ (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0)).
       * eapply srun_tau; [apply next_KTrap_throw|apply srun_refl].
       * eapply ERel_at; [exact L|exact W|exact Hh|apply Hx|exact HS].
     + rewrite next_KTrap_throw in E. discriminate.
     + cbn in Rc. discriminate. }
 apply KRel_iff. intros j L w' W. split; [|intros x s0 s HS; apply Th; assumption].
 intros v0 v s0 s HV HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_running.
 - reflexivity.
 - unfold nonterm. rewrite next_KTrap_ret. exact I.
 - intros x. cbn [kont mem]. apply Th; [lia|exact W|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E. rewrite next_KTrap_ret in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KTrap_ret|apply srun_refl]|]. eapply ret_at; eauto.
 - intros q kk r E. rewrite next_KTrap_ret in E. discriminate.
Qed.

(* ---------- two frames with the same next move ---------- *)
(* c and d are both running, have the same next move and store, and continuations that differ
   only in their top frame, neither a trap. Then they are observably interchangeable. *)
Definition swap_ok (c d : config) : Prop :=
 next_r R P c = next_r R P d /\ running_state c = true /\ running_state d = true /\ mem c = mem d /\
 exists f f' K, kont c = f :: K /\ kont d = f' :: K /\ nontrap f = true /\ nontrap f' = true.

Lemma swap_sym : forall c d, swap_ok c d -> swap_ok d c.
Proof.
 intros c d (E & Rc & Rd & M & f & f' & K & Kc & Kd & N & N').
 split; [symmetry; exact E|split; [exact Rd|split; [exact Rc|split; [symmetry; exact M|]]]].
 exists f', f, K. repeat split; assumption.
Qed.

Lemma runs_swap : forall c d n t c', swap_ok c d -> runs n c t c' ->
 (n = 0%nat /\ c' = c) \/ (exists x, t = [] /\ c' = Cfg (Throw x) (kont c) (mem c)) \/ runs n d t c'.
Proof.
 intros c d n t c' Sw Hr. destruct Sw as (E & Rc & Rd & M & f & f' & K & Kc & Kd & N & N').
 inversion Hr as [c2|n' c2 l c1 t' c3 St Hr']; subst; [left; auto|right].
 destruct (step_r_cases _ _ _ St) as [[E1 ->]|[(q & kk & r & E1 & -> & ->)|(r & x & _ & Rx & -> & ->)]].
 - right. econstructor; [apply step_r_tau; rewrite <- E; exact E1|exact Hr'].
 - right. econstructor; [apply step_r_io; rewrite <- E; exact E1|exact Hr'].
 - inversion Hr' as [c4|n'' c4 l2 c5 t'' c6 St2 Hr'']; subst.
   + left. exists x. auto.
   + right. rewrite Kc in St2.
     destruct (step_r_cases _ _ _ St2) as [[E2 ->]|[(q & kk & r2 & E2 & _)|(r2 & y & Rc2 & _)]].
     * rewrite throw_frame_next in E2 by exact N. injection E2 as <-.
       econstructor; [eapply step_r_resource; [exact Rd|exact Rx]|].
       econstructor; [apply step_r_tau; rewrite Kd; apply throw_frame_next; exact N'|].
       rewrite <- M. exact Hr''.
     * rewrite throw_frame_next in E2 by exact N. discriminate.
     * cbn in Rc2. discriminate.
Qed.

Lemma srun_swap : forall c d t c', swap_ok c d -> srun d t c' ->
 (t = [] /\ c' = d) \/ (exists x, t = [] /\ c' = Cfg (Throw x) (kont d) (mem d)) \/ srun c t c'.
Proof.
 intros c d t c' Sw H. destruct (srun_runs sealed _ _ _ H) as [n Hn].
 destruct (runs_swap d c n t c' (swap_sym _ _ Sw) Hn) as [[-> ->]|[Hx|Hc]].
 - left. inversion Hn; auto.
 - right; left; exact Hx.
 - right; right. eapply runs_srun; exact Hc.
Qed.

Lemma swap_src : forall c0 d0 t, swap_ok c0 d0 ->
 (forall v s, srun d0 t (Cfg (Ret v) [] s) -> srun c0 t (Cfg (Ret v) [] s)) /\
 (forall x s, srun d0 t (Cfg (Throw x) [] s) -> srun c0 t (Cfg (Throw x) [] s)) /\
 (forall c' why, srun d0 t c' -> next_r R P c' = MWrong why -> exists c'', srun c0 t c'' /\ next_r R P c'' = MWrong why).
Proof.
 intros c0 d0 t Sw. pose proof Sw as (E & Rc & Rd & M & f & f' & K & Kc & Kd & N & N').
 split; [|split].
 - intros v s H. destruct (srun_swap _ _ _ _ Sw H) as [[_ Ed]|[[x [_ Ed]]|Hc]]; [| |exact Hc].
   + rewrite <- Ed in Kd. discriminate.
   + discriminate.
 - intros x s H. destruct (srun_swap _ _ _ _ Sw H) as [[_ Ed]|[[y [_ Ed]]|Hc]]; [| |exact Hc].
   + rewrite <- Ed in Kd. discriminate.
   + injection Ed as _ Ek _. rewrite Kd in Ek. discriminate.
 - intros c' why H Ew. destruct (srun_swap _ _ _ _ Sw H) as [[-> ->]|[[y [-> ->]]|Hc]].
   + exists c0. split; [apply srun_refl|]. rewrite E. exact Ew.
   + rewrite Kd in Ew. rewrite throw_frame_next in Ew by exact N'. discriminate.
   + exists c'. auto.
Qed.

Theorem ObsT_swap : forall k w c0 d0 c d, swap_ok c0 d0 -> swap_ok c d -> ObsT k w d0 d -> ObsT k w c0 c.
Proof.
 intros k w c0 d0 c d S0 S1 H n t c' L Hr. destruct (swap_src c0 d0 t S0) as (A0 & B0 & C0).
 pose proof S1 as (E & Rc & Rd & M & f & f' & K & Kc & Kd & N & N').
 destruct (runs_swap _ _ _ _ _ S1 Hr) as [[-> ->]|[[x [-> ->]]|Hd]].
 - assert (t = []) as -> by (inversion Hr; auto).
   split; [|split].
   + intros v s Ec. rewrite Ec in Kc. discriminate.
   + intros x s Ec. rewrite Ec in Kc. discriminate.
   + intros why Ew. rewrite E in Ew. assert (R0 : runs 0 d [] d) by constructor.
     destruct (H 0%nat [] d L R0) as (_ & _ & Cw).
     destruct (Cw why Ew) as (c1 & why0 & S2 & W2). destruct (C0 c1 why0 S2 W2) as (c2 & S3 & W3).
     exists c2, why0. auto.
 - split; [|split].
   + intros v s Ec. discriminate.
   + intros y s Ec. injection Ec as _ Ek _. rewrite Kc in Ek. discriminate.
   + intros why Ew. rewrite Kc in Ew. rewrite throw_frame_next in Ew by exact N. discriminate.
 - destruct (H n t c' L Hd) as (A & B & C). split; [|split].
   + intros v s Ec. destruct (A v s Ec) as (v0 & s0 & w' & S2 & X). exists v0, s0, w'. split; [apply A0; exact S2|exact X].
   + intros x s Ec. destruct (B x s Ec) as (s0 & w' & S2 & X). exists s0, w'. split; [apply B0; exact S2|exact X].
   + intros why Ew. destruct (C why Ew) as (c1 & why0 & S2 & W2). destruct (C0 c1 why0 S2 W2) as (c2 & S3 & W3).
     exists c2, why0. auto.
Qed.

(* ---------- applications ---------- *)
(* The application relation for function values f0 and f under continuations K0 and K: applied
   to related arguments, with related stores, at every index up to k and world above w. It is a
   hypothesis of the application frames below; proving it is compat_app's and compat_call's. *)
Definition AppRel (k : nat) (w : world) (f0 f : value) (K0 K : list frame) : Prop :=
 forall j w' args0 args s0 s, (j <= k)%nat -> wext w w' -> Forall2 (VRel j w') args0 args -> SRel j w' s0 s ->
  ObsT j w' (Cfg (Ret f0) (KApply args0 :: K0) s0) (Cfg (Ret f) (KApply args :: K) s).
Definition AppAll (k : nat) (w : world) (K0 K : list frame) : Prop :=
 forall j w' f0 f, (j <= k)%nat -> wext w w' -> VRel j w' f0 f -> AppRel j w' f0 f K0 K.

Lemma AppRel_mono : forall k j w w' f0 f K0 K, (j <= k)%nat -> wext w w' -> AppRel k w f0 f K0 K -> AppRel j w' f0 f K0 K.
Proof.
 intros k j w w' f0 f K0 K L W H j' w'' a0 a s0 s L' W' A S0.
 apply H; [lia|eapply wext_trans; eauto|exact A|exact S0].
Qed.

Lemma AppAll_mono : forall k j w w' K0 K, (j <= k)%nat -> wext w w' -> AppAll k w K0 K -> AppAll j w' K0 K.
Proof.
 intros k j w w' K0 K L W H j' w'' f0 f L' W' V. apply H; [lia|eapply wext_trans; eauto|exact V].
Qed.

Lemma Forall2_rev2 : forall {A B} (Q : A -> B -> Prop) l1 l2, Forall2 Q l1 l2 -> Forall2 Q (rev l1) (rev l2).
Proof.
 intros A B Q l1 l2 F. induction F as [|a b l1 l2 Qab F IH]; cbn; [constructor|].
 apply Forall2_app; [exact IH|constructor; [exact Qab|constructor]].
Qed.

Theorem KRel_KApply : forall k w args0 args K0 K, KRel k w K0 K -> AppAll k w K0 K -> Forall2 (VRel k w) args0 args ->
 KRel k w (KApply args0 :: K0) (KApply args :: K).
Proof.
 intros k w args0 args K0 K HK HA F. apply KRel_push; [exact HK|reflexivity|reflexivity|].
 intros j w' v0 v s0 s L W HV HS. apply (HA j w' v0 v L W HV j w'); [lia|eapply wext_self; exact HS| |exact HS].
 eapply Forall2_VRel_mono; [exact L|exact W|exact F].
Qed.

Ltac swap_tac := split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]];
 do 3 eexists; split; [reflexivity|split; [reflexivity|split; reflexivity]].

Lemma next_KArgs_cons : forall v fv done a rest rho K s,
 next_r R P (Cfg (Ret v) (KArgs fv done (a :: rest) rho :: K) s) = MTau (Cfg (Eval rho a) (KArgs fv (v :: done) rest rho :: K) s).
Proof. reflexivity. Qed.
Lemma next_KCallArgs_cons : forall v g done a rest rho K s,
 next_r R P (Cfg (Ret v) (KCallArgs g done (a :: rest) rho :: K) s) = MTau (Cfg (Eval rho a) (KCallArgs g (v :: done) rest rho :: K) s).
Proof. reflexivity. Qed.
Lemma next_KHead_cons : forall v a rest rho K s,
 next_r R P (Cfg (Ret v) (KHead (a :: rest) rho :: K) s) = MTau (Cfg (Eval rho a) (KArgs v [] rest rho :: K) s).
Proof. reflexivity. Qed.

(* The argument frame of a dynamic application: the next argument, or the application itself. *)
Theorem KRel_KArgs : forall rest0 rest k w fv0 fv done0 done rho0 rho K0 K, KRel k w K0 K -> AppRel k w fv0 fv K0 K ->
 Forall2 (VRel k w) done0 done -> Forall2 (fun a0 a => ERel k w rho0 a0 rho a) rest0 rest ->
 KRel k w (KArgs fv0 done0 rest0 rho0 :: K0) (KArgs fv done rest rho :: K).
Proof.
 induction rest0 as [|a0 rest0 IH]; intros [|a rest] k w fv0 fv done0 done rho0 rho K0 K HK HA Hd Hr.
 - apply KRel_push; [exact HK|reflexivity|reflexivity|]. intros j w' v0 v s0 s L W HV HS.
   apply (ObsT_swap _ _ _ (Cfg (Ret fv0) (KApply (rev (v0 :: done0)) :: K0) s0) _ (Cfg (Ret fv) (KApply (rev (v :: done)) :: K) s));
    [swap_tac|swap_tac|].
   apply HA; [exact L|exact W| |exact HS]. apply Forall2_rev2. constructor; [exact HV|].
   eapply Forall2_VRel_mono; [exact L|exact W|exact Hd].
 - inversion Hr.
 - inversion Hr.
 - inversion Hr as [|x y l l' Ha Hrest]; subst.
   apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros; eexists; apply next_KArgs_cons].
   intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KArgs_cons in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KArgs_cons|apply srun_refl]|].
   eapply (ERel_at (S j)); [apply le_n|eapply wext_self; exact HS|eapply ERel_mono; [exact L|exact W|exact Ha]| |exact HS].
   apply IH; [eapply KRel_mono; [exact L|exact W|exact HK]|eapply AppRel_mono; [exact L|exact W|exact HA]| |].
   + constructor; [exact HV|]. eapply Forall2_VRel_mono; [exact L|exact W|exact Hd].
   + eapply Forall2_ERel_mono; [exact L|exact W|exact Hrest].
Qed.

(* The head frame of a dynamic application. *)
Theorem KRel_KHead : forall k w args0 args rho0 rho K0 K, KRel k w K0 K -> AppAll k w K0 K ->
 Forall2 (fun a0 a => ERel k w rho0 a0 rho a) args0 args -> KRel k w (KHead args0 rho0 :: K0) (KHead args rho :: K).
Proof.
 intros k w args0 args rho0 rho K0 K HK HA F. destruct F as [|a0 a args0 args Ha F].
 - apply KRel_push; [exact HK|reflexivity|reflexivity|]. intros j w' v0 v s0 s L W HV HS.
   apply (ObsT_swap _ _ _ (Cfg (Ret v0) (KApply [] :: K0) s0) _ (Cfg (Ret v) (KApply [] :: K) s)); [swap_tac|swap_tac|].
   apply (HA j w' v0 v L W HV j w'); [lia|eapply wext_self; exact HS|constructor|exact HS].
 - apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros; eexists; apply next_KHead_cons].
   intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KHead_cons in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KHead_cons|apply srun_refl]|].
   eapply (ERel_at (S j)); [apply le_n|eapply wext_self; exact HS|eapply ERel_mono; [exact L|exact W|exact Ha]| |exact HS].
   apply KRel_KArgs; [eapply KRel_mono; [exact L|exact W|exact HK]|apply (HA (S j) w' v0 v L W HV)|constructor|].
   eapply Forall2_ERel_mono; [exact L|exact W|exact F].
Qed.

(* The argument frame of a named call: the next argument, or the call, which is the application of
   the partial application of g to no arguments. *)
Theorem KRel_KCallArgs : forall rest0 rest k w g done0 done rho0 rho K0 K, KRel k w K0 K ->
 AppRel k w (VPartial g []) (VPartial g []) K0 K -> Forall2 (VRel k w) done0 done ->
 Forall2 (fun a0 a => ERel k w rho0 a0 rho a) rest0 rest ->
 KRel k w (KCallArgs g done0 rest0 rho0 :: K0) (KCallArgs g done rest rho :: K).
Proof.
 induction rest0 as [|a0 rest0 IH]; intros [|a rest] k w g done0 done rho0 rho K0 K HK HA Hd Hr.
 - apply KRel_push; [exact HK|reflexivity|reflexivity|]. intros j w' v0 v s0 s L W HV HS.
   apply (ObsT_swap _ _ _ (Cfg (Ret (VPartial g [])) (KApply (rev (v0 :: done0)) :: K0) s0) _
     (Cfg (Ret (VPartial g [])) (KApply (rev (v :: done)) :: K) s)); [swap_tac|swap_tac|].
   apply HA; [exact L|exact W| |exact HS]. apply Forall2_rev2. constructor; [exact HV|].
   eapply Forall2_VRel_mono; [exact L|exact W|exact Hd].
 - inversion Hr.
 - inversion Hr.
 - inversion Hr as [|x y l l' Ha Hrest]; subst.
   apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros; eexists; apply next_KCallArgs_cons].
   intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KCallArgs_cons in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KCallArgs_cons|apply srun_refl]|].
   eapply (ERel_at (S j)); [apply le_n|eapply wext_self; exact HS|eapply ERel_mono; [exact L|exact W|exact Ha]| |exact HS].
   apply IH; [eapply KRel_mono; [exact L|exact W|exact HK]|eapply AppRel_mono; [exact L|exact W|exact HA]| |].
   + constructor; [exact HV|]. eapply Forall2_VRel_mono; [exact L|exact W|exact Hd].
   + eapply Forall2_ERel_mono; [exact L|exact W|exact Hrest].
Qed.

(* ======================= ERel-form anti-reduction ======================= *)
(* If, from any stores related at an index up to k, the source steps silently, under any
   continuation, to a configuration related to the target expression (the environment may change,
   and the store may gain one-sided cells), the source expression is related to the target one. *)
Theorem ERel_anti : forall k w rho0 e0 rho e,
 (forall j w' K0 s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s -> exists rho0' e0' s0',
    srun (Cfg (Eval rho0 e0) K0 s0) [] (Cfg (Eval rho0' e0') K0 s0') /\ SRel j w' s0' s /\ ERel j w' rho0' e0' rho e) ->
 ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e H. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct (H j w' K0 s0 s L W HS) as (rho0' & e0' & s0' & S0 & HS' & He).
 eapply ObsT_anti; [exact S0|]. eapply ERel_apply; [exact He|apply le_n|eapply wext_self; exact HS'|exact HK|exact HS'].
Qed.

Corollary ERel_anti_same : forall k w rho0 e0 rho0' e0' rho e,
 (forall K0 s0, srun (Cfg (Eval rho0 e0) K0 s0) [] (Cfg (Eval rho0' e0') K0 s0)) ->
 ERel k w rho0' e0' rho e -> ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho0' e0' rho e Hs He. apply ERel_anti. intros j w' K0 s0 s L W HS.
 exists rho0', e0', s0. split; [apply Hs|split; [exact HS|eapply ERel_mono; eauto]].
Qed.

Lemma sval_next : forall rho a v K s, sval rho a = Some v -> next_r R P (Cfg (Eval rho a) K s) = MTau (Cfg (Ret v) K s).
Proof.
 intros rho a v K s H. destruct a; cbn in H; try discriminate; try (injection H as <-; reflexivity).
 change (MTau (Cfg (match lookup x rho with Some v => Ret v | None => Throw (XUnboundVar x) end) K s) = MTau (Cfg (Ret v) K s)).
 rewrite H. reflexivity.
Qed.

Theorem ERel_anti_let : forall k w x a0 b0 v0 rho0 rho e, sval rho0 a0 = Some v0 ->
 ERel k w ((x, v0) :: rho0) b0 rho e -> ERel k w rho0 (ELet x a0 b0) rho e.
Proof.
 intros k w x a0 b0 v0 rho0 rho e Hv He. eapply ERel_anti_same; [|exact He]. intros K0 s0.
 eapply srun_tau; [reflexivity|]. eapply srun_tau; [apply sval_next; exact Hv|].
 eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

Theorem ERel_anti_if : forall k w c0 a0 b0 bv rho0 rho e, sval rho0 c0 = Some (VBool bv) ->
 ERel k w rho0 (if bv then a0 else b0) rho e -> ERel k w rho0 (EIf c0 a0 b0) rho e.
Proof.
 intros k w c0 a0 b0 bv rho0 rho e Hv He. destruct bv; (eapply ERel_anti_same; [|exact He]); intros K0 s0;
 (eapply srun_tau; [reflexivity|]); (eapply srun_tau; [apply sval_next; exact Hv|]);
 (eapply srun_tau; [reflexivity|apply srun_refl]).
Qed.

Theorem ERel_anti_cond : forall k w c0 b0 rest0 bv rho0 rho e, sval rho0 c0 = Some (VBool bv) ->
 ERel k w rho0 (if bv then b0 else ECond rest0) rho e -> ERel k w rho0 (ECond ((c0, b0) :: rest0)) rho e.
Proof.
 intros k w c0 b0 rest0 bv rho0 rho e Hv He. destruct bv; (eapply ERel_anti_same; [|exact He]); intros K0 s0;
 (eapply srun_tau; [reflexivity|]); (eapply srun_tau; [apply sval_next; exact Hv|]);
 (eapply srun_tau; [reflexivity|apply srun_refl]).
Qed.

Theorem ERel_anti_type : forall k w a0 rho0 rho e, ERel k w rho0 a0 rho e -> ERel k w rho0 (EType a0) rho e.
Proof.
 intros k w a0 rho0 rho e He. eapply ERel_anti_same; [|exact He]. intros K0 s0.
 eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

Lemma call_named_user : forall f ps b args K s, lookup f (gfuns s) = Some (FUser ps b) ->
 List.length args = List.length ps -> call_named_r R P f args K s = MTau (Cfg (Eval (combine ps args) b) K s).
Proof.
 intros f ps b args K s E L. unfold call_named_r. rewrite E. unfold arity_mismatch.
 change (arity_errors R) with true. rewrite L, Nat.eqb_refl, Nat.ltb_irrefl. cbn [andb negb].
 rewrite <- L, firstn_all, skipn_all. reflexivity.
Qed.

Lemma srun_callargs : forall f rho rest vs done v K s c', Forall2 (fun a u => sval rho a = Some u) rest vs ->
 call_named_r R P f (rev done ++ v :: vs) K s = MTau c' ->
 srun (Cfg (Ret v) (KCallArgs f done rest rho :: K) s) [] c'.
Proof.
 intros f rho rest vs done v K s c' F. revert done v. induction F as [|a u rest vs Ha F IH]; intros done v E.
 - eapply srun_tau; [exact E|apply srun_refl].
 - eapply srun_tau; [apply next_KCallArgs_cons|]. eapply srun_tau; [apply sval_next; exact Ha|].
   apply IH. rewrite <- E. f_equal. cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Theorem ERel_anti_call : forall k w f ps b0 args vs rho0 rho e, In (f, FUser ps b0) D ->
 Forall2 (fun a u => sval rho0 a = Some u) args vs -> List.length vs = List.length ps ->
 ERel k w (combine ps vs) b0 rho e -> ERel k w rho0 (ECall f args) rho e.
Proof.
 intros k w f ps b0 args vs rho0 rho e I F L He. apply ERel_anti. intros j w' K0 s0 s Lj W HS.
 assert (Ef : lookup f (gfuns s0) = Some (FUser ps b0)) by (destruct HS as (_ & H0 & _); apply H0; exact I).
 exists (combine ps vs), b0, s0. split; [|split; [exact HS|eapply ERel_mono; eauto]].
 destruct F as [|a u args vs Ha F].
 - apply (srun_tau _ (Cfg (Eval (combine ps []) b0) K0 s0)); [exact (call_named_user f ps b0 [] K0 s0 Ef L)|apply srun_refl].
 - eapply srun_tau; [reflexivity|]. eapply srun_tau; [apply sval_next; exact Ha|].
   apply srun_callargs with (vs := vs); [exact F|]. apply call_named_user; [exact Ef|exact L].
Qed.

Theorem SRel_with_cell : forall k w s0 s, SRel k w s0 s -> SRel k w (with_cell s0) s.
Proof.
 intros k w s0 s (W & H0 & H1 & G & Gv & Hp).
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact G|split; [exact Gv|]]]]].
 intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. split; [|split; [exact N|exact F]].
 cbn. rewrite nth_error_app1; [exact N0|]. apply nth_error_Some. congruence.
Qed.

(* Lambda application: the closure takes a fresh cell on the source side only. *)
Theorem ERel_anti_app_lam : forall k w x b0 a0 v0 rho0 rho e, sval rho0 a0 = Some v0 ->
 (forall l, ERel k w ((x, v0) :: (id_key, VVec l) :: rho0) b0 rho e) ->
 ERel k w rho0 (EApp (ELam x b0) [a0]) rho e.
Proof.
 intros k w x b0 a0 v0 rho0 rho e Hv He. apply ERel_anti. intros j w' K0 s0 s L W HS.
 exists ((x, v0) :: (id_key, VVec (List.length (heap s0))) :: rho0), b0, (with_cell s0).
 split; [|split; [apply SRel_with_cell; exact HS|eapply ERel_mono; eauto]].
 eapply srun_tau; [reflexivity|]. eapply srun_tau; [reflexivity|]. eapply srun_tau; [reflexivity|].
 eapply srun_tau; [apply sval_next; exact Hv|]. eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

(* ======================= world reachability ======================= *)
Lemma GVal_ptrs : forall w v0 v, GVal w v0 v -> Forall2 (fun l0 l => In (l0, l) w) (vptrs v0) (vptrs v).
Proof.
 intros w v0. induction v0; intros v H; destruct v; cbn in H; try contradiction; cbn [vptrs].
 6: { destruct H as [H1 H2]. apply Forall2_app; [apply IHv0_1|apply IHv0_2]; assumption. }
 6: { constructor; [exact H|constructor]. }
 all: constructor.
Qed.

(* Related values point to related locations, pointwise. *)
Theorem VRel_ptrs : forall k w v0 v, VRel k w v0 v -> Forall2 (fun l0 l => In (l0, l) w) (vptrs v0) (vptrs v).
Proof. intros k w v0 v H. apply GVal_ptrs. exact (JitKRefGround.JitKRefGround.VRel_ground sealed D k w v0 v H). Qed.

Lemma Forall2_in_l : forall {A B} (Q : A -> B -> Prop) l1 l2 x, Forall2 Q l1 l2 -> In x l1 -> exists y, In y l2 /\ Q x y.
Proof.
 intros A B Q l1 l2 x F. induction F as [|a b l1 l2 Qab F IH]; intro I; [contradiction|].
 destruct I as [<-|I]; [exists b; split; [left; reflexivity|exact Qab]|].
 destruct (IH I) as (z & Iz & Qz). exists z. split; [right; exact Iz|exact Qz].
Qed.

Lemma Forall2_in_r : forall {A B} (Q : A -> B -> Prop) l1 l2 y, Forall2 Q l1 l2 -> In y l2 -> exists x, In x l1 /\ Q x y.
Proof.
 intros A B Q l1 l2 y F. induction F as [|a b l1 l2 Qab F IH]; intro I; [contradiction|].
 destruct I as [<-|I]; [exists a; split; [left; reflexivity|exact Qab]|].
 destruct (IH I) as (z & Iz & Qz). exists z. split; [right; exact Iz|exact Qz].
Qed.

Lemma len_map : forall {A B} (f : A -> B) l, List.length (map f l) = List.length l.
Proof. intros A B f l. induction l as [|a l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma len_seq : forall n m, List.length (seq m n) = n.
Proof. induction n as [|n IH]; intro m; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma below_length : forall (S : list nat) n, NoDup S -> (forall l, In l S -> (l < n)%nat) -> (List.length S <= n)%nat.
Proof.
 intros S n N H. rewrite <- (len_seq n 0). apply NoDup_incl_length; [exact N|].
 intros l I. apply in_seq. specialize (H l I). lia.
Qed.

(* JitEqBudgetWalk.closed_in, with vptrs for data_ptrs (the same text). *)
Definition closed_set (h : list (list value)) (S : list nat) : Prop :=
 forall p xs, In p S -> nth_error h p = Some xs -> forall l, In l (flat_map vptrs xs) -> In l S.

(* World reachability: under SRel, the world's source side and its target side are each closed
   under the vector pointers of their cells, duplicate-free, allocated, and of the same size, the
   world's length, so at most either heap's length. With VRel_ptrs, every cell = can reach from two
   related values is in the world, on each side, through the world's bijection. *)
Theorem world_closed : forall k w s0 s, SRel k w s0 s ->
 closed_set (heap s0) (map fst w) /\ closed_set (heap s) (map snd w) /\
 NoDup (map fst w) /\ NoDup (map snd w) /\ List.length (map fst w) = List.length (map snd w) /\
 (forall l0, In l0 (map fst w) -> (l0 < List.length (heap s0))%nat) /\
 (forall l, In l (map snd w) -> (l < List.length (heap s))%nat) /\
 (List.length w <= List.length (heap s0))%nat /\ (List.length w <= List.length (heap s))%nat.
Proof.
 intros k w s0 s HS. pose proof HS as ([F1 F2] & _ & _ & _ & _ & Hp).
 assert (A0 : forall l0, In l0 (map fst w) -> (l0 < List.length (heap s0))%nat).
 { intros l0 I. apply in_map_iff in I as [[a b] [Ea I]]. cbn in Ea. subst a.
   destruct (Hp _ _ I) as (c0 & c & N0 & _). apply nth_error_Some. congruence. }
 assert (A1 : forall l, In l (map snd w) -> (l < List.length (heap s))%nat).
 { intros l I. apply in_map_iff in I as [[a b] [Eb I]]. cbn in Eb. subst b.
   destruct (Hp _ _ I) as (c0 & c & _ & N & _). apply nth_error_Some. congruence. }
 assert (C0 : closed_set (heap s0) (map fst w)).
 { intros p xs I N l Il. apply in_map_iff in I as [[a b] [Ea I]]. cbn in Ea. subst a.
   destruct (Hp _ _ I) as (c0 & c & N0 & N1 & F). rewrite N in N0. injection N0 as <-.
   apply in_flat_map in Il as [x [Ix Il]]. destruct (Forall2_in_l _ _ _ _ F Ix) as (y & Iy & Vxy).
   destruct (Forall2_in_l _ _ _ _ (VRel_ptrs _ _ _ _ Vxy) Il) as (l' & _ & Iw).
   apply in_map_iff. exists (l, l'). split; [reflexivity|exact Iw]. }
 assert (C1 : closed_set (heap s) (map snd w)).
 { intros p xs I N l Il. apply in_map_iff in I as [[a b] [Eb I]]. cbn in Eb. subst b.
   destruct (Hp _ _ I) as (c0 & c & N0 & N1 & F). rewrite N in N1. injection N1 as <-.
   apply in_flat_map in Il as [y [Iy Il]]. destruct (Forall2_in_r _ _ _ _ F Iy) as (x & Ix & Vxy).
   destruct (Forall2_in_r _ _ _ _ (VRel_ptrs _ _ _ _ Vxy) Il) as (l' & _ & Iw).
   apply in_map_iff. exists (l', l). split; [reflexivity|exact Iw]. }
 split; [exact C0|split; [exact C1|split; [exact F1|split; [exact F2|split]]]].
 - rewrite !len_map. reflexivity.
 - split; [exact A0|split; [exact A1|split]].
   + rewrite <- (len_map fst w). apply below_length; assumption.
   + rewrite <- (len_map snd w). apply below_length; assumption.
Qed.

(* JitEqBudgetStep.din and closed_in, same text: each cell of S is allocated and its data points into S. *)
Fixpoint dptr (A : nat -> Prop) (v : value) : Prop := match v with
 | VCons a b => dptr A a /\ dptr A b
 | VVec l => A l
 | _ => True end.
Definition closed_alloc (h : list (list value)) (S : list nat) : Prop :=
 forall p, In p S -> exists xs, nth_error h p = Some xs /\ Forall (dptr (fun l => In l S)) xs.

Lemma dptr_vptrs : forall (A : nat -> Prop) v, (forall l, In l (vptrs v) -> A l) -> dptr A v.
Proof.
 intros A v. induction v; intro H; cbn [vptrs dptr] in *; try exact I.
 - split; [apply IHv1|apply IHv2]; intros l I; apply H; apply in_or_app; auto.
 - apply H. left. reflexivity.
Qed.

(* world_closed in JitEqBudgetStep's form (closed_in), on each side. Not derivable from SRel:
   JitEqBudgetStep's S-local lok (lok_in), since VRel relates closures by behaviour and identity,
   not by the contents of their environments (SRel_lok_refuted, below). *)
Theorem world_closed_alloc : forall k w s0 s, SRel k w s0 s ->
 closed_alloc (heap s0) (map fst w) /\ closed_alloc (heap s) (map snd w).
Proof.
 intros k w s0 s HS. destruct (world_closed k w s0 s HS) as (C0 & C1 & _ & _ & _ & A0 & A1 & _).
 split.
 - intros p I. pose proof (A0 p I) as L. destruct (nth_error (heap s0) p) as [xs|] eqn:N; [|apply nth_error_None in N; lia].
   exists xs. split; [reflexivity|]. apply Forall_forall. intros x Ix. apply dptr_vptrs. intros l Il.
   apply (C0 p xs I N). apply in_flat_map. exists x. auto.
 - intros p I. pose proof (A1 p I) as L. destruct (nth_error (heap s) p) as [xs|] eqn:N; [|apply nth_error_None in N; lia].
   exists xs. split; [reflexivity|]. apply Forall_forall. intros x Ix. apply dptr_vptrs. intros l Il.
   apply (C1 p xs I N). apply in_flat_map. exists x. auto.
Qed.

(* ======================= sealed definitions are stable ======================= *)
Definition pgf (s : store) (o : pout) : Prop := match o with ORet _ s' => gfuns s' = gfuns s | _ => True end.

Ltac dmatch := match goal with |- context [match ?x with _ => _ end] =>
 lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x end end.

(* No primitive changes the function table. *)
Theorem prim_gfuns : forall p args s,
 match prim_rule_r R P p args s with PDone o => pgf s o | PIO q kk => forall r, pgf s (kk r) end.
Proof.
 intros p args s. destruct p; unfold prim_rule_r, prim_rule, rule_intern, rule_pos, rule_tlstr, rule_cn, rule_str,
  rule_stringp, rule_n_to_string_r, rule_string_to_n, rule_set, rule_value, rule_simple_error,
  rule_error_to_string, rule_cons, rule_hd, rule_tl, rule_consp, rule_equal_r, rule_eval_kl, rule_absvector,
  rule_address_set, rule_address_get, rule_absvectorp, rule_write_byte_r, rule_write_byte, rule_read_byte,
  rule_open, rule_close, rule_get_time_r, rule_get_time, rule_arith_r, rule_div_r, rule_cmp, rule_numberp,
  ret, throw, dom, io_fail;
  repeat (intros; cbn -[kl_eq_r]; dmatch); cbn; auto.
Qed.

Definition move_gf (s : store) (m : move) : Prop := match m with
 | MTau c' => gfuns (mem c') = gfuns s | MIO _ kk => forall r, gfuns (mem (kk r)) = gfuns s | _ => True end.

Lemma pout_config_gf : forall o rest K s, pgf s o -> gfuns (mem (pout_config P o rest K s)) = gfuns s.
Proof. intros o rest K s H. destruct o; cbn in *; destruct rest; first [exact H|exact eq_refl]. Qed.

(* jit_rules has no port primitive, so an unbound name only raises. *)
Theorem jit_port_prim_none : forall g, port_prim R g = None.
Proof. reflexivity. Qed.

Lemma call_gf : forall g args K s, move_gf s (call_named_r R P g args K s).
Proof.
 intros g args K s. unfold call_named_r. destruct (lookup g (gfuns s)) as [[p|ps b]|].
 - destruct (arity_mismatch R (List.length args) (prim_arity p)); [exact eq_refl|].
   destruct (Nat.ltb (List.length args) (prim_arity p)); [exact eq_refl|].
   unfold prim_move_r. pose proof (prim_gfuns p (firstn (prim_arity p) args) s) as H.
   destruct (prim_rule_r R P p (firstn (prim_arity p) args) s).
   + apply pout_config_gf; exact H.
   + intro r. apply pout_config_gf. apply H.
 - destruct (arity_mismatch R (List.length args) (List.length ps)); [exact eq_refl|].
   destruct (Nat.ltb (List.length args) (List.length ps)); [exact eq_refl|].
   destruct (skipn (List.length ps) args); exact eq_refl.
 - rewrite jit_port_prim_none. exact eq_refl.
Qed.

Lemma apply_gf : forall f args K s, move_gf s (apply_value_r R P f args K s).
Proof.
 intros f args K s. destruct f; try exact (call_gf _ _ _ _); destruct args as [|a rest]; try exact eq_refl.
 destruct rest; exact eq_refl.
Qed.

(* A step either keeps the function table or adds a definition that defun_allowed admitted. *)
Definition gfd (s s' : store) : Prop :=
 gfuns s' = gfuns s \/ exists f d, defun_allowed R s f = true /\ gfuns s' = (f, d) :: gfuns s.
Definition move_gfd (s : store) (m : move) : Prop := match m with
 | MTau c' => gfd s (mem c') | MIO _ kk => forall r, gfd s (mem (kk r)) | _ => True end.

Lemma move_gf_gfd : forall s m, move_gf s m -> move_gfd s m.
Proof. intros s [c'|q kk|o|why] H; cbn in *; auto; [left; exact H|intro r; left; apply H]. Qed.

Lemma next_gfd : forall c, move_gfd (mem c) (next_r R P c).
Proof.
 intros [[rho e|v|x|r|ev|why] K s]; cbn [mem].
 - change (move_gfd s (eval_move_r R P rho e K s)). destruct e; try (apply move_gf_gfd; exact eq_refl).
   + destruct clauses as [|[c b] l]; apply move_gf_gfd; exact eq_refl.
   + unfold eval_move_r. destruct (defun_allowed R s f) eqn:Da; [destruct (nodupb params)|];
      unfold move_gfd, gfd; cbn [mem gfuns].
     * right. eexists _, _. split; [exact Da|reflexivity].
     * left; reflexivity.
     * left; reflexivity.
   + destruct args; apply move_gf_gfd; [exact (call_gf _ _ _ _)|exact eq_refl].
 - destruct K as [|f K]; [exact I|]. change (move_gfd s (ret_move_r R P v f K s)).
   apply move_gf_gfd. destruct f; try exact eq_refl.
   + destruct v; try exact eq_refl. destruct b0; exact eq_refl.
   + destruct v; try exact eq_refl. destruct b0; exact eq_refl.
   + destruct args; [exact (apply_gf _ _ _ _)|exact eq_refl].
   + destruct rest; [exact (apply_gf _ _ _ _)|exact eq_refl].
   + destruct rest; [exact (call_gf _ _ _ _)|exact eq_refl].
   + exact (apply_gf _ _ _ _).
 - destruct K as [|f K]; [exact I|]. change (move_gfd s (throw_move x f K s)).
   apply move_gf_gfd. destruct f; exact eq_refl.
 - change (move_gfd s (match resource_exn R r with Some x => MTau (Cfg (Throw x) K s) | None => MFinal (ResourceOut r) end)).
   destruct (resource_exn R r); [apply move_gf_gfd; exact eq_refl|exact I].
 - destruct ev; exact I.
 - exact I.
Qed.

Lemma step_gfd : forall c l c', step_r R P c l c' -> gfd (mem c) (mem c').
Proof.
 intros c l c' H. destruct H as [c c' E|c q kk r E|c r x _ _].
 - pose proof (next_gfd c) as G. rewrite E in G. exact G.
 - pose proof (next_gfd c) as G. rewrite E in G. apply G.
 - left; reflexivity.
Qed.

(* jit_rules' defun_allowed refuses every sealed name, so no step changes a sealed name's
   function: not defun, not defun through eval-kl (its form runs eval_move_r's EDefun rule), not a
   primitive, and there is no port primitive. *)
Theorem sealed_step : forall c l c' f, step_r R P c l c' -> In f sealed ->
 lookup f (gfuns (mem c')) = lookup f (gfuns (mem c)).
Proof.
 intros c l c' f H I. destruct (step_gfd _ _ _ H) as [E|(g & d & Da & E)]; rewrite E; [reflexivity|].
 cbn [lookup]. destruct (text_eqb f g) eqn:T; [|reflexivity]. exfalso. apply text_eqb_eq in T. subst g.
 change (negb (is_fixed_name f || existsb (text_eqb f) sealed) = true) in Da.
 apply negb_true_iff, orb_false_iff in Da as [_ Da].
 assert (existsb (text_eqb f) sealed = true) as Ex by (apply existsb_exists; exists f; split; [exact I|apply text_eqb_refl]).
 congruence.
Qed.

Theorem sealed_stable : sealed_stable_statement.
Proof.
 intros c t c' f H I. unfold JitKRef.JitKRef.srun in H.
 induction H as [c|c l c1 t c2 St H IH]; [reflexivity|]. rewrite IH. eapply sealed_step; eauto.
Qed.

Theorem storehas_stable : storehas_stable_statement.
Proof.
 intros c t c' [Fs _] H SH f d I. rewrite (sealed_stable c t c' f H).
 - apply SH; exact I.
 - rewrite Forall_forall in Fs. exact (Fs (f, d) I).
Qed.
End Equiv.

(* ======================= two directions that do not hold ======================= *)
(* SRel is not monotone up in wext: the empty store is related to itself at the empty world but
   not at [(0,0)], whose pair has no cell. SRel_wext_cells is the true form. *)
Theorem SRel_wext_refuted : forall sealed k,
 ~ (forall w w' s0 s, wext w w' -> JitKRef.JitKRef.SRel sealed [] k w s0 s -> JitKRef.JitKRef.SRel sealed [] k w' s0 s).
Proof.
 intros sealed k H. set (s := Store [] [] []).
 assert (A : JitKRef.JitKRef.SRel sealed [] k [] s s).
 { unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
   split; [split; constructor|split; [intros f d []|split; [intros f d []|split; [reflexivity|split; [constructor|]]]]].
   intros l0 l []. }
 assert (W : wext [] [(0%nat, 0%nat)]).
 { split; [intros a []|split; (constructor; [intros []|constructor])]. }
 destruct (H [] [(0%nat, 0%nat)] s s W A) as (_ & _ & _ & _ & _ & Hp).
 destruct (Hp 0%nat 0%nat (or_introl eq_refl)) as (c0 & c & N & _). discriminate.
Qed.

(* ObsT is not monotone up in wext: a returned value with the empty store is observed at the empty
   world, but not at [(0,0)], which GStore would need a cell for. ObsT_wext_anti is the true
   direction. *)
Theorem ObsT_wext_refuted : forall sealed,
 ~ (forall k w w' c0 c, wext w w' -> JitKRef.JitKRef.ObsT sealed k w c0 c -> JitKRef.JitKRef.ObsT sealed k w' c0 c).
Proof.
 intros sealed H. set (s := Store [] [] []). set (c := Cfg (Ret VNil) [] s).
 assert (A : JitKRef.JitKRef.ObsT sealed 1 [] c c).
 { apply JitKRefGround.JitKRefGround.obs_top_ret; [split; constructor|exact I|].
   split; [reflexivity|split; [constructor|intros l0 l []]]. }
 assert (W : wext [] [(0%nat, 0%nat)]).
 { split; [intros a []|split; (constructor; [intros []|constructor])]. }
 assert (R0 : JitKRef.JitKRef.runs sealed 0 c [] c) by constructor.
 destruct (H 1%nat [] [(0%nat, 0%nat)] c c W A 0%nat [] c ltac:(lia) R0) as (Hr & _ & _).
 destruct (Hr VNil s eq_refl) as (v0 & s0 & w' & _ & [Iw _] & _ & _ & _ & Hc).
 destruct (Hc 0%nat 0%nat (Iw _ (or_introl eq_refl))) as (c1 & c2 & _ & N & _). discriminate.
Qed.
(* S-local lok (JitEqBudgetStep.lok_in) does not follow from SRel: at index 0 two frozen closures are
   related by identity alone, so a world cell may hold one whose environment points past the heap. *)
Theorem SRel_lok_refuted : forall sealed,
 ~ (forall k w s0 s, JitKRef.JitKRef.SRel sealed [] k w s0 s -> forall p xs, In p (map fst w) ->
     nth_error (heap s0) p = Some xs -> lok (List.length (heap s0)) xs).
Proof.
 intros sealed H. set (v := VFrozen ENil [([], VVec 1)]). set (s := Store [[v]] [] []).
 assert (A : JitKRef.JitKRef.SRel sealed [] 0 [(0%nat, 0%nat)] s s).
 { unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
   split; [split; (constructor; [intros []|constructor])|].
   split; [intros f d []|split; [intros f d []|split; [reflexivity|split; [constructor|]]]].
   intros l0 l [E|[]]. injection E as <- <-. exists [v], [v]. split; [reflexivity|split; [reflexivity|]].
   constructor; [|constructor]. rewrite (JitKRefGround.JitKRefGround.VRel_unfold sealed [] 0).
   split; [exact I|intros j L; lia]. }
 pose proof (H 0%nat [(0%nat, 0%nat)] s s A 0%nat [v] (or_introl eq_refl) eq_refl) as Ok.
 inversion Ok as [|? ? Hv _]. cbn in Hv. lia.
Qed.

End JitKRefBase.
