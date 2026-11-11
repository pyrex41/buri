(* Shen/JIT Phase 2: KRef's compatibility lemmas for closures and dynamic application (kref-clo).
   The statements compat_lambda_statement, compat_freeze_statement and compat_app_statement are
   JitKTerm.v's; this file re-opens Section Equiv with JitKTerm.v's Variables and proves:

   - lam_core, frz_core: an ELam (EFreeze) pair is related at index k when the bodies are related
     at every j < k, in every world above w, in the environments the closures will run in: the
     captured environment behind the identity cell (tagged_env) and, for a lambda, the argument.
     Each side allocates one cell (object_identity); the world is extended with the fresh pair,
     fresh by world_closed (every location of the world is allocated on its side), and the pair's
     cells are [] on both sides. same_id holds because both closure_id's are the new locations.
     KRef relating only g does NOT get in the way: VBody's body clause is about the bodies run in
     environments related on g, the argument name and the identity key, and the identity key is
     related because the new pair is in every larger world.
   - compat_lambda, compat_freeze: the JitKTerm statements, without any induction hypothesis.
   - compat_lambda_lt, compat_freeze_lt: the same expression on both sides at index k, from
     fund_below k, in fund_below's scope form: the cases JitKTermFund's induction needs.
   - app_rel: AppAll at every index up to k for continuations related there, from fund_below k and
     prim_compat_statement, by induction on the index. Closures: VBody's body clause at the lower
     index (the target's application step pays it); over-application is the KApply frame, related
     by the induction hypothesis. Arity errors and non-callable heads (symbols, data) raise the
     same exception on both sides. A partial application calls through the function table, which
     SRel makes equal on both sides: an unbound name raises XUndefinedFun (jit_rules_nr has no port
     primitive), a user function runs the same body in environments related on its parameters
     (fund_below), a primitive gives related outcomes (prim_compat_statement), including eval-kl's
     expression (fund_below in the empty environment) and IO requests, and a short call returns a
     related partial application. This is the general handling OB-JIT-DEV-APPLY asks for.
   - compat_app_core, compat_app_lt: EApp at index k from its head and arguments related below k.
   - compat_app_of_fund: compat_app_statement from fund_gen_statement and prim_compat_statement.

   NOT proved here: compat_app_statement outright. A partial application of a store function or
   primitive runs code outside the expression, so it needs the fundamental property at lower
   indices and the primitives' compatibility: compat_app_of_fund takes fund_gen_statement and
   prim_compat_statement (JitKTermFund and JitKTermPrim own them) as premises. compat_call and
   compat_defun are not in this file. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKTerm JitKTermGround JitKTermBase.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKTermCompatClo.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKTerm.JitKTerm
 JitKTermGround.JitKTermGround JitKTermBase.JitKTermBase.

(* What continue_with gives under jit_profile, which has no stack limit. *)
Definition kapp (rest : list value) (K : list frame) : list frame :=
 match rest with [] => K | _ => KApply rest :: K end.

Lemma continue_jit : forall rest K c s, continue_with jit_profile rest K c s = Cfg c (kapp rest K) s.
Proof. intros [|a rest] K c s; reflexivity. Qed.

Lemma Forall2_firstn : forall {A B} (Q : A -> B -> Prop) n l0 l, Forall2 Q l0 l -> Forall2 Q (firstn n l0) (firstn n l).
Proof.
 intros A B Q n. induction n as [|n IH]; intros l0 l F; [constructor|].
 destruct F; cbn; constructor; auto.
Qed.

Lemma Forall2_skipn : forall {A B} (Q : A -> B -> Prop) n l0 l, Forall2 Q l0 l -> Forall2 Q (skipn n l0) (skipn n l).
Proof.
 intros A B Q n. induction n as [|n IH]; intros l0 l F; [exact F|].
 destruct F; cbn; [constructor|auto].
Qed.

Lemma len_firstn : forall {A} n (l : list A), List.length (firstn n l) = Nat.min n (List.length l).
Proof. intros A n. induction n as [|n IH]; intros [|x l]; cbn; auto. Qed.

(* Lookup in combine ps vs: related values for every parameter when there are enough of them, and
   nothing for a name that is not a parameter. *)
Lemma lookup_combine_rel : forall (Q : value -> value -> Prop) ps l0 l, Forall2 Q l0 l ->
 (List.length ps <= List.length l0)%nat -> forall y, In y ps ->
 exists v0 v, lookup y (combine ps l0) = Some v0 /\ lookup y (combine ps l) = Some v /\ Q v0 v.
Proof.
 intros Q ps. induction ps as [|p ps IH]; intros l0 l F L y I; [destruct I|].
 destruct F as [|a0 a l0 l Qa F]; cbn in L; [lia|]. cbn.
 destruct (text_eqb y p) eqn:E; [exists a0, a; auto|].
 destruct I as [<-|I]; [rewrite text_eqb_refl in E; discriminate|]. apply IH; [exact F|lia|exact I].
Qed.

Lemma lookup_combine_notin : forall ps (l : list value) y, ~ In y ps -> lookup y (combine ps l) = None.
Proof.
 intros ps. induction ps as [|p ps IH]; intros l y N; [reflexivity|]. destruct l as [|a l]; [reflexivity|].
 cbn. destruct (text_eqb y p) eqn:E.
 - apply text_eqb_eq in E. subst. exfalso. apply N. left. reflexivity.
 - apply IH. intro I. apply N. right. exact I.
Qed.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Notation srun := (JitKTerm.JitKTerm.srun sealed).
Notation runs := (JitKTerm.JitKTerm.runs sealed).
Notation ObsT := (JitKTerm.JitKTerm.ObsT sealed).
Notation SRel_with := (JitKTerm.JitKTerm.SRel_with D).
Notation KRel_with := (JitKTerm.JitKTerm.KRel_with sealed D).
Notation ERel_with := (JitKTerm.JitKTerm.ERel_with sealed D).
Notation VBody := (JitKTerm.JitKTerm.VBody sealed D).
Notation VRelF := (JitKTerm.JitKTerm.VRelF sealed D).
Notation VRel := (JitKTerm.JitKTerm.VRel sealed D).
Notation SRel := (JitKTerm.JitKTerm.SRel sealed D).
Notation KRel := (JitKTerm.JitKTerm.KRel sealed D).
Notation ERel := (JitKTerm.JitKTerm.ERel sealed D).
Notation KRef := (JitKTerm.JitKTerm.KRef sealed D).
Notation D_wf := (JitKTerm.JitKTerm.D_wf sealed D).
Notation fund_below := (JitKTerm.JitKTerm.fund_below sealed D).
Notation fund_gen_statement := (JitKTerm.JitKTerm.fund_gen_statement sealed D).
Notation PoutRel := (JitKTerm.JitKTerm.PoutRel sealed D).
Notation PrimOutRel := (JitKTerm.JitKTerm.PrimOutRel sealed D).
Notation prim_compat_statement := (JitKTerm.JitKTerm.prim_compat_statement sealed D).
Notation compat_lambda_statement := (JitKTerm.JitKTerm.compat_lambda_statement sealed D).
Notation compat_freeze_statement := (JitKTerm.JitKTerm.compat_freeze_statement sealed D).
Notation compat_app_statement := (JitKTerm.JitKTerm.compat_app_statement sealed D).
Notation AppRel := (JitKTermBase.JitKTermBase.AppRel sealed D).
Notation AppAll := (JitKTermBase.JitKTermBase.AppAll sealed D).
Notation nonterm := (JitKTermBase.JitKTermBase.nonterm sealed).
Notation VRelF_index := (JitKTermGround.JitKTermGround.VRelF_index sealed D).
Notation VRel_unfold := (JitKTermGround.JitKTermGround.VRel_unfold sealed D).
Notation KRel_throw := (JitKTermBase.JitKTermBase.KRel_throw sealed D).
Notation KRel_ret := (JitKTermBase.JitKTermBase.KRel_ret sealed D).
Notation KRel_down := (JitKTermBase.JitKTermBase.KRel_down sealed D).
Notation KRel_mono := (JitKTermBase.JitKTermBase.KRel_mono sealed D).
Notation KRel_wext := (JitKTermBase.JitKTermBase.KRel_wext sealed D).
Notation SRel_down := (JitKTermBase.JitKTermBase.SRel_down sealed D).
Notation SRel_wf := (JitKTermBase.JitKTermBase.SRel_wf sealed D).
Notation ERel_iff := (JitKTermBase.JitKTermBase.ERel_iff sealed D).
Notation ERel_apply := (JitKTermBase.JitKTermBase.ERel_apply sealed D).
Notation ERel_push := (JitKTermBase.JitKTermBase.ERel_push sealed D).
Notation KRel_throw_frame := (JitKTermBase.JitKTermBase.KRel_throw_frame sealed D).
Notation KRel_KApply := (JitKTermBase.JitKTermBase.KRel_KApply sealed D).
Notation KRel_KHead := (JitKTermBase.JitKTermBase.KRel_KHead sealed D).
Notation VRel_wext := (JitKTermBase.JitKTermBase.VRel_wext sealed D).
Notation VRel_down := (JitKTermBase.JitKTermBase.VRel_down sealed D).
Notation VRel_mono := (JitKTermBase.JitKTermBase.VRel_mono sealed D).
Notation Forall2_VRel_mono := (JitKTermBase.JitKTermBase.Forall2_VRel_mono sealed D).
Notation wext_self := (JitKTermBase.JitKTermBase.wext_self sealed D).
Notation world_closed := (JitKTermBase.JitKTermBase.world_closed sealed D).
Notation EnvRel_mono := (JitKTermBase.JitKTermBase.EnvRel_mono sealed D).
Notation KRef_scope := (JitKTermBase.JitKTermBase.KRef_scope sealed D).
Notation AppAll_mono := (JitKTermBase.JitKTermBase.AppAll_mono sealed D).
Notation ObsT_running := (JitKTermBase.JitKTermBase.ObsT_running sealed).
Notation ObsT_anti_io := (JitKTermBase.JitKTermBase.ObsT_anti_io sealed).
Notation srun_tau := (JitKTermBase.JitKTermBase.srun_tau sealed).
Notation srun_refl := (JitKTermBase.JitKTermBase.srun_refl sealed).
Notation step_r_cases := (JitKTermBase.JitKTermBase.step_r_cases sealed).
Notation wrong_match := (JitKTermBase.JitKTermBase.wrong_match sealed).
Notation ObsT_wext_anti := (JitKTermBase.JitKTermBase.ObsT_wext_anti sealed).
Notation ObsT_0 := (JitKTermBase.JitKTermBase.ObsT_0 sealed).
Notation ObsT_step := (JitKTermBase.JitKTermBase.ObsT_step sealed).
Notation jit_port_prim_none := (JitKTermBase.JitKTermBase.jit_port_prim_none sealed).
Notation ERel_with_ext := (JitKTermGround.JitKTermGround.ERel_with_ext sealed D).
Notation VBody_partial := (JitKTermGround.JitKTermGround.VBody_partial sealed D).

(* ======================= helpers ======================= *)
Lemma fund_below_down : forall k j, (j <= k)%nat -> fund_below k -> fund_below j.
Proof. intros k j L F i Li. apply F. lia. Qed.

Lemma VRel_vec : forall k w l0 l, In (l0, l) w -> VRel k w (VVec l0) (VVec l).
Proof. intros k w l0 l I. rewrite VRel_unfold. exact I. Qed.

Lemma closure_id_tagged : forall rho s, closure_id (tagged_env rho s) = Some (List.length (heap s)).
Proof. intros rho s. reflexivity. Qed.

(* Each side allocates one cell: the world grows by the fresh pair, whose cells are both []. *)
Theorem SRel_alloc : forall k w s0 s, SRel k w s0 s ->
 let w' := (List.length (heap s0), List.length (heap s)) :: w in
 wext w w' /\ SRel k w' (with_cell s0) (with_cell s).
Proof.
 intros k w s0 s HS w'. destruct (world_closed k w s0 s HS) as (_ & _ & N0 & N1 & _ & A0 & A1 & _).
 assert (Wf : wf_world w').
 { split; cbn; constructor; auto.
   - intro I. specialize (A0 _ I). lia.
   - intro I. specialize (A1 _ I). lia. }
 assert (Wx : wext w w') by (split; [intros p I; right; exact I|exact Wf]).
 split; [exact Wx|].
 destruct HS as (_ & H0 & H1 & G & Gv & Hp).
 split; [exact Wf|split; [exact H0|split; [exact H1|split; [exact G|split]]]].
 - eapply Forall2_impl; [|exact Gv]. intros [x a] [y b] [E A]; split; [exact E|]. eapply VRel_wext; eauto.
 - intros l0 l [Ep|I].
   + injection Ep as <- <-. exists [], []. cbn. rewrite !nth_error_app2 by lia. rewrite !Nat.sub_diag.
     split; [reflexivity|split; [reflexivity|constructor]].
   + destruct (Hp _ _ I) as (c0 & c & E0 & E & F). exists c0, c. cbn.
     rewrite !nth_error_app1 by (apply nth_error_Some; congruence).
     split; [exact E0|split; [exact E|]]. eapply Forall2_impl; [|exact F]. intros a b; apply VRel_wext; exact Wx.
Qed.

(* ======================= lambda and freeze ======================= *)
(* The body of a lambda pair: related at every j < k in every world above w, given the closures'
   identity locations related there and related arguments. *)
Definition LamBody (k : nat) (w : world) (x0 : name) (rho0 : lenv) (b0 : expr) (x : name) (rho : lenv) (b : expr) : Prop :=
 forall j w' l0 l a0 a, (j < k)%nat -> wext w w' -> In (l0, l) w' -> VRel j w' a0 a ->
  ERel j w' ((x0, a0) :: (id_key, VVec l0) :: rho0) b0 ((x, a) :: (id_key, VVec l) :: rho) b.

Definition FrzBody (k : nat) (w : world) (rho0 : lenv) (b0 : expr) (rho : lenv) (b : expr) : Prop :=
 forall j w' l0 l, (j < k)%nat -> wext w w' -> In (l0, l) w' ->
  ERel j w' ((id_key, VVec l0) :: rho0) b0 ((id_key, VVec l) :: rho) b.

Lemma next_lam : forall rho x b K s,
 next_r R P (Cfg (Eval rho (ELam x b)) K s) = MTau (Cfg (Ret (VLam x b (tagged_env rho s))) K (with_cell s)).
Proof. reflexivity. Qed.

Lemma next_frz : forall rho b K s,
 next_r R P (Cfg (Eval rho (EFreeze b)) K s) = MTau (Cfg (Ret (VFrozen b (tagged_env rho s))) K (with_cell s)).
Proof. reflexivity. Qed.

Lemma ERel_norm : forall j i w r0 e0 r e, (i <= j)%nat -> ERel i w r0 e0 r e -> ERel_with (VRelF j) i w r0 e0 r e.
Proof.
 intros j i w r0 e0 r e L H. eapply ERel_with_ext; [|exact H]. intros i' Li'.
 rewrite !VRelF_index by lia. reflexivity.
Qed.

(* A closure value of either kind returned from an allocation, related at every index j whose
   body hypotheses hold below j. *)
Lemma VRel_lam_tagged : forall j w x0 b0 rho0 s0 x b rho s,
 In (List.length (heap s0), List.length (heap s)) w ->
 (forall i w' a0 a, (i < j)%nat -> wext w w' -> VRel i w' a0 a ->
   ERel i w' ((x0, a0) :: tagged_env rho0 s0) b0 ((x, a) :: tagged_env rho s) b) ->
 VRel j w (VLam x0 b0 (tagged_env rho0 s0)) (VLam x b (tagged_env rho s)).
Proof.
 intros j w x0 b0 rho0 s0 x b rho s I Hb. rewrite VRel_unfold. cbn [JitKTerm.JitKTerm.VBody]. split.
 - unfold same_id. rewrite !closure_id_tagged. exact I.
 - intros i Li w' W a0 a A. destruct j as [|j]; [lia|].
   rewrite VRelF_index in A by lia. apply ERel_norm; [lia|]. apply Hb; assumption.
Qed.

Lemma VRel_frz_tagged : forall j w b0 rho0 s0 b rho s,
 In (List.length (heap s0), List.length (heap s)) w ->
 (forall i w', (i < j)%nat -> wext w w' -> ERel i w' (tagged_env rho0 s0) b0 (tagged_env rho s) b) ->
 VRel j w (VFrozen b0 (tagged_env rho0 s0)) (VFrozen b (tagged_env rho s)).
Proof.
 intros j w b0 rho0 s0 b rho s I Hb. rewrite VRel_unfold. cbn [JitKTerm.JitKTerm.VBody]. split.
 - unfold same_id. rewrite !closure_id_tagged. exact I.
 - intros i Li w' W. destruct j as [|j]; [lia|]. apply ERel_norm; [lia|]. apply Hb; assumption.
Qed.

(* The allocation step: from the closures' values related at the extended world, the two
   allocations are related. *)
Lemma alloc_step : forall k w rho0 e0 rho e K0 K s0 s (mk0 mk : lenv -> value),
 (forall K0 s0, next_r R P (Cfg (Eval rho0 e0) K0 s0) = MTau (Cfg (Ret (mk0 (tagged_env rho0 s0))) K0 (with_cell s0))) ->
 (forall K s, next_r R P (Cfg (Eval rho e) K s) = MTau (Cfg (Ret (mk (tagged_env rho s))) K (with_cell s))) ->
 KRel (S k) w K0 K -> SRel (S k) w s0 s ->
 (forall w', wext w w' -> In (List.length (heap s0), List.length (heap s)) w' ->
    VRel k w' (mk0 (tagged_env rho0 s0)) (mk (tagged_env rho s))) ->
 ObsT (S k) w (Cfg (Eval rho0 e0) K0 s0) (Cfg (Eval rho e) K s).
Proof.
 intros k w rho0 e0 rho e K0 K s0 s mk0 mk E0 E HK HS HV. apply ObsT_running.
 - reflexivity.
 - unfold JitKTermBase.JitKTermBase.nonterm. rewrite E. exact I.
 - intros x. cbn [kont mem]. apply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite E in E1. injection E1 as <-.
   eexists; split; [eapply srun_tau; [apply E0|apply srun_refl]|].
   destruct (SRel_alloc (S k) w s0 s HS) as [Wx HS'].
   eapply ObsT_wext_anti; [exact Wx|]. apply KRel_ret.
   + eapply KRel_mono; [|exact Wx|exact HK]. lia.
   + apply HV; [exact Wx|left; reflexivity].
   + eapply SRel_down; [|exact HS']. lia.
 - intros q kk r E1. rewrite E in E1. discriminate.
Qed.

Theorem lam_core : forall k w x0 rho0 b0 x rho b, LamBody k w x0 rho0 b0 x rho b ->
 ERel k w rho0 (ELam x0 b0) rho (ELam x b).
Proof.
 intros k w x0 rho0 b0 x rho b Hb. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|].
 apply (alloc_step j w' rho0 (ELam x0 b0) rho (ELam x b) K0 K s0 s (VLam x0 b0) (VLam x b));
  [intros; apply next_lam|intros; apply next_lam|exact HK|exact HS|].
 intros w2 W2 I. apply VRel_lam_tagged; [exact I|]. intros i w3 a0 a Li W3 A.
 apply Hb; [lia|eapply wext_trans; [exact W|eapply wext_trans; eauto]|apply (proj1 W3); exact I|exact A].
Qed.

Theorem frz_core : forall k w rho0 b0 rho b, FrzBody k w rho0 b0 rho b ->
 ERel k w rho0 (EFreeze b0) rho (EFreeze b).
Proof.
 intros k w rho0 b0 rho b Hb. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|].
 apply (alloc_step j w' rho0 (EFreeze b0) rho (EFreeze b) K0 K s0 s (VFrozen b0) (VFrozen b));
  [intros; apply next_frz|intros; apply next_frz|exact HK|exact HS|].
 intros w2 W2 I. apply VRel_frz_tagged; [exact I|]. intros i w3 Li W3.
 apply Hb; [lia|eapply wext_trans; [exact W|eapply wext_trans; eauto]|apply (proj1 W3); exact I].
Qed.

(* Environments a closure body runs in: the captured ones behind the identity cell, and the argument. *)
Lemma EnvRel_tagged : forall j w g rho0 rho l0 l, EnvRel_with (VRel j) w g rho0 rho -> In (l0, l) w ->
 EnvRel_with (VRel j) w (id_key :: g) ((id_key, VVec l0) :: rho0) ((id_key, VVec l) :: rho).
Proof.
 intros j w g rho0 rho l0 l HE I y Iy. cbn. destruct (text_eqb y id_key) eqn:E.
 - exists (VVec l0), (VVec l). split; [reflexivity|split; [reflexivity|apply VRel_vec; exact I]].
 - destruct Iy as [<-|Iy]; [rewrite text_eqb_refl in E; discriminate|]. apply HE. exact Iy.
Qed.

Lemma EnvRel_arg : forall j w g rho0 rho x a0 a, EnvRel_with (VRel j) w g rho0 rho -> VRel j w a0 a ->
 EnvRel_with (VRel j) w (x :: g) ((x, a0) :: rho0) ((x, a) :: rho).
Proof.
 intros j w g rho0 rho x a0 a HE A y Iy. cbn. destruct (text_eqb y x) eqn:E.
 - exists a0, a. auto.
 - destruct Iy as [<-|Iy]; [rewrite text_eqb_refl in E; discriminate|]. apply HE. exact Iy.
Qed.

(* compat_lambda and compat_freeze follow from the body's KRef, with no induction hypothesis. *)
Theorem compat_lambda : compat_lambda_statement.
Proof.
 intros g x b0 b Hb k w rho0 rho Wf HE. apply lam_core. intros j w' l0 l a0 a Lj W I A.
 apply (KRef_scope (x :: g) (x :: id_key :: g)); [intros y [<-|Iy]; [left; reflexivity|right; right; exact Iy]| |apply W|].
 - exact Hb.
 - apply (EnvRel_arg j w' (id_key :: g) _ _ x); [|exact A].
   apply EnvRel_tagged; [|exact I]. eapply EnvRel_mono; [|exact W|exact HE]. lia.
Qed.

Theorem compat_freeze : compat_freeze_statement.
Proof.
 intros g b0 b Hb k w rho0 rho Wf HE. apply frz_core. intros j w' l0 l Lj W I.
 apply (KRef_scope g (id_key :: g)); [intros y Iy; right; exact Iy|exact Hb|apply W|].
 apply EnvRel_tagged; [|exact I]. eapply EnvRel_mono; [|exact W|exact HE]. lia.
Qed.

(* The scope condition of fund_below for an expression in environments rho0 and rho. *)
Definition FvOk (g : list name) (rho0 rho : lenv) (e : expr) : Prop :=
 forall y, In y (fv e) -> In y g \/ (lookup y rho0 = None /\ lookup y rho = None).

Lemma FvOk_tagged : forall g rho0 rho l0 l e, FvOk g rho0 rho e ->
 FvOk (id_key :: g) ((id_key, VVec l0) :: rho0) ((id_key, VVec l) :: rho) e.
Proof.
 intros g rho0 rho l0 l e H y Iy. cbn. destruct (text_eqb y id_key) eqn:E.
 - apply text_eqb_eq in E. subst. left; left; reflexivity.
 - destruct (H y Iy) as [I|N]; [left; right; exact I|right; exact N].
Qed.

Lemma FvOk_lam : forall g rho0 rho x a0 a b, FvOk g rho0 rho (ELam x b) ->
 FvOk (x :: g) ((x, a0) :: rho0) ((x, a) :: rho) b.
Proof.
 intros g rho0 rho x a0 a b H y Iy. cbn. destruct (text_eqb y x) eqn:E.
 - apply text_eqb_eq in E. subst. left; left; reflexivity.
 - assert (I : In y (fv (ELam x b))) by (cbn; apply filter_In; split; [exact Iy|rewrite E; reflexivity]).
   destruct (H y I) as [I'|N]; [left; right; exact I'|right; exact N].
Qed.

(* The reflexive forms JitKTermFund's induction uses, from fund_below k. *)
Theorem compat_lambda_lt : forall k w g rho0 rho x b, fund_below k -> wf_world w ->
 EnvRel_with (VRel k) w g rho0 rho -> FvOk g rho0 rho (ELam x b) ->
 ERel k w rho0 (ELam x b) rho (ELam x b).
Proof.
 intros k w g rho0 rho x b F Wf HE Hfv. apply lam_core. intros j w' l0 l a0 a Lj W I A.
 apply (F j Lj w' (x :: id_key :: g)); [apply W| |].
 - apply (EnvRel_arg j w' (id_key :: g) _ _ x); [|exact A].
   apply EnvRel_tagged; [|exact I]. eapply EnvRel_mono; [|exact W|exact HE]. lia.
 - intros y Iy. cbn. destruct (text_eqb y x) eqn:E.
   + apply text_eqb_eq in E. subst. left; left; reflexivity.
   + assert (I' : In y (fv (ELam x b))) by (cbn; apply filter_In; split; [exact Iy|rewrite E; reflexivity]).
     destruct (FvOk_tagged g rho0 rho l0 l _ Hfv y I') as [I2|N]; [left; right; exact I2|right; exact N].
Qed.

Theorem compat_freeze_lt : forall k w g rho0 rho b, fund_below k -> wf_world w ->
 EnvRel_with (VRel k) w g rho0 rho -> FvOk g rho0 rho (EFreeze b) ->
 ERel k w rho0 (EFreeze b) rho (EFreeze b).
Proof.
 intros k w g rho0 rho b F Wf HE Hfv. apply frz_core. intros j w' l0 l Lj W I.
 apply (F j Lj w' (id_key :: g)); [apply W| |].
 - apply EnvRel_tagged; [|exact I]. eapply EnvRel_mono; [|exact W|exact HE]. lia.
 - apply FvOk_tagged. exact Hfv.
Qed.

(* ======================= dynamic application ======================= *)
(* Two moves related at index j: both silent to configurations related at j, or the same IO
   request with continuations related at j for every response. *)
Definition MoveRel (j : nat) (w : world) (m0 m : move) : Prop :=
 match m0, m with
 | MTau c0, MTau c => ObsT j w c0 c
 | MIO q0 kk0, MIO q kk => q0 = q /\ forall r, ObsT j w (kk0 r) (kk r)
 | _, _ => False end.

Lemma next_KApply : forall f args K s,
 next_r R P (Cfg (Ret f) (KApply args :: K) s) = apply_value_r R P f args K s.
Proof. reflexivity. Qed.

(* The application step: the target's step pays one index. *)
Theorem app_step : forall j w f0 f args0 args K0 K s0 s, KRel j w K0 K -> SRel j w s0 s ->
 MoveRel j w (apply_value_r R P f0 args0 K0 s0) (apply_value_r R P f args K s) ->
 ObsT (S j) w (Cfg (Ret f0) (KApply args0 :: K0) s0) (Cfg (Ret f) (KApply args :: K) s).
Proof.
 intros j w f0 f args0 args K0 K s0 s HK HS M. apply ObsT_running.
 - reflexivity.
 - unfold JitKTermBase.JitKTermBase.nonterm. rewrite next_KApply.
   destruct (apply_value_r R P f0 args0 K0 s0), (apply_value_r R P f args K s); cbn in M; try contradiction; exact I.
 - intros x. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|reflexivity|reflexivity|apply le_n|eapply wext_self; exact HS|exact HS].
 - intros c1 E1. rewrite next_KApply in E1. rewrite E1 in M.
   destruct (apply_value_r R P f0 args0 K0 s0) as [c0'| | |] eqn:E0; cbn in M; try contradiction.
   exists c0'. split; [eapply srun_tau; [rewrite next_KApply; exact E0|apply srun_refl]|exact M].
 - intros q kk r E1. rewrite next_KApply in E1. rewrite E1 in M.
   destruct (apply_value_r R P f0 args0 K0 s0) as [|q0 kk0| |] eqn:E0; cbn in M; try contradiction.
   destruct M as [<- M]. exists (kk0 r). split; [|apply M].
   change [EvIO q0 r] with (trace_of (Obs (EvIO q0 r)) ++ []). econstructor; [|constructor].
   apply step_r_io. rewrite next_KApply. exact E0.
Qed.

Lemma throw_rel : forall j w x K0 K s0 s, KRel j w K0 K -> SRel j w s0 s ->
 MoveRel j w (MTau (Cfg (Throw x) K0 s0)) (MTau (Cfg (Throw x) K s)).
Proof. intros. apply KRel_throw; assumption. Qed.

(* A resource failure a primitive reports. Under jit_rules_nr it is not catchable: Fail r is the
   terminal MFinal (ResourceOut r) on both sides, which no clause of ObsT observes. *)
Lemma fail_obs : forall j w r K0 K s0 s, KRel j w K0 K -> SRel j w s0 s ->
 ObsT j w (Cfg (Fail r) K0 s0) (Cfg (Fail r) K s).
Proof.
 intros j w r K0 K s0 s _ _ n t c' _ Hr. inversion Hr as [c|n' c l c1 t' c2 St _]; subst.
 - split; [|split].
   + intros v s' E; discriminate.
   + intros x s' E; discriminate.
   + intros why N. destruct r; cbn in N; discriminate.
 - exfalso. inversion St; subst; destruct r; cbn in *; discriminate.
Qed.

Lemma wrong_obs : forall j w why0 why K0 K s0 s, ObsT j w (Cfg (Wrong why0) K0 s0) (Cfg (Wrong why) K s).
Proof.
 intros. eapply wrong_match; [reflexivity|]. exists (Cfg (Wrong why0) K0 s0), why0.
 split; [apply srun_refl|reflexivity].
Qed.

Lemma KRel_kapp : forall j w K0 K rest0 rest, KRel j w K0 K -> AppAll j w K0 K -> Forall2 (VRel j w) rest0 rest ->
 KRel j w (kapp rest0 K0) (kapp rest K).
Proof.
 intros j w K0 K rest0 rest HK HA F. destruct F as [|a0 a rest0 rest A F]; [exact HK|].
 apply KRel_KApply; [exact HK|exact HA|constructor; assumption].
Qed.

(* A primitive's outcomes, related by PoutRel, continue to related configurations. *)
Lemma pout_obs : forall j w o0 o rest0 rest K0 K s0 s, fund_below (S j) ->
 KRel j w K0 K -> AppAll j w K0 K -> Forall2 (VRel j w) rest0 rest -> SRel j w s0 s ->
 PoutRel j w o0 o -> ObsT j w (pout_config P o0 rest0 K0 s0) (pout_config P o rest K s).
Proof.
 intros j w o0 o rest0 rest K0 K s0 s F HK HA Hr HS Ho.
 destruct o0 as [v0 s0'|x0|e0|r0|why0], o as [v s'|x|e|r|why]; cbn in Ho; try contradiction; cbn [pout_config].
 - destruct Ho as (w' & W & HV & HS'). rewrite !continue_jit. eapply ObsT_wext_anti; [exact W|].
   apply KRel_ret; [|exact HV|exact HS']. apply KRel_kapp.
   + eapply KRel_wext; eauto.
   + eapply AppAll_mono; [apply le_n|exact W|exact HA].
   + eapply Forall2_VRel_mono; [apply le_n|exact W|exact Hr].
 - subst. apply KRel_throw; assumption.
 - subst. rewrite !continue_jit. eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS|apply KRel_kapp; assumption|exact HS].
   apply (F j (Nat.lt_succ_diag_r j) w []); [eapply SRel_wf; exact HS|intros y []|].
   intros y _. right. split; reflexivity.
 - subst. apply fail_obs; assumption.
 - apply wrong_obs.
Qed.

Lemma VRel_partial_j : forall j w g vs0 vs, Forall2 (VRel j w) vs0 vs -> VRel j w (VPartial g vs0) (VPartial g vs).
Proof.
 intros j w g vs0 vs F. rewrite VRel_unfold. apply VBody_partial. split; [reflexivity|].
 eapply Forall2_impl; [|exact F]. intros a b H. rewrite VRel_unfold in H. exact H.
Qed.

(* A call through the function table, with related arguments: SRel makes both tables equal. *)
Theorem call_rel : forall j w g vs0 vs K0 K s0 s, fund_below (S j) -> prim_compat_statement ->
 KRel j w K0 K -> AppAll j w K0 K -> Forall2 (VRel j w) vs0 vs -> SRel j w s0 s ->
 MoveRel j w (call_named_r R P g vs0 K0 s0) (call_named_r R P g vs K s).
Proof.
 intros j w g vs0 vs K0 K s0 s F PC HK HA Hv HS.
 assert (Gf : gfuns s0 = gfuns s) by apply HS.
 assert (Ln : List.length vs0 = List.length vs) by (eapply Forall2_length; exact Hv).
 unfold call_named_r. rewrite Gf. destruct (lookup g (gfuns s)) as [[p|ps body]|].
 - rewrite Ln. destruct (arity_mismatch R (List.length vs) (prim_arity p)); [apply throw_rel; assumption|].
   destruct (Nat.ltb (List.length vs) (prim_arity p)); [apply KRel_ret; [exact HK|apply VRel_partial_j; exact Hv|exact HS]|].
   unfold prim_move_r.
   pose proof (proj1 (PC j w) p _ _ s0 s (Forall2_firstn _ (prim_arity p) _ _ Hv) HS) as Hp.
   destruct (prim_rule_r R P p (firstn (prim_arity p) vs0) s0) as [o0|q0 c0],
            (prim_rule_r R P p (firstn (prim_arity p) vs) s) as [o|q c]; cbn in Hp |- *; try contradiction.
   + apply pout_obs; [exact F|exact HK|exact HA|apply Forall2_skipn; exact Hv|exact HS|exact Hp].
   + destruct Hp as [<- Hp]. split; [reflexivity|]. intro r.
     apply pout_obs; [exact F|exact HK|exact HA|apply Forall2_skipn; exact Hv|exact HS|apply Hp].
 - rewrite Ln. destruct (arity_mismatch R (List.length vs) (List.length ps)); [apply throw_rel; assumption|].
   destruct (Nat.ltb (List.length vs) (List.length ps)) eqn:Lt; [apply KRel_ret; [exact HK|apply VRel_partial_j; exact Hv|exact HS]|].
   apply Nat.ltb_ge in Lt. cbn [MoveRel]. rewrite !continue_jit.
   eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS|apply KRel_kapp; [exact HK|exact HA|apply Forall2_skipn; exact Hv]|exact HS].
   apply (F j (Nat.lt_succ_diag_r j) w ps); [eapply SRel_wf; exact HS| |].
   + intros y Iy. apply (lookup_combine_rel (VRel j w)); [apply Forall2_firstn; exact Hv| |exact Iy].
     rewrite len_firstn. lia.
   + intros y _. destruct (in_dec (list_eq_dec N.eq_dec) y ps) as [I|N]; [left; exact I|right].
     split; apply lookup_combine_notin; exact N.
 - rewrite (jit_port_prim_none g). apply throw_rel; assumption.
Qed.

(* The application relation at every index up to k, by induction on the index. *)
Definition AppAt (j : nat) : Prop := forall w K0 K f0 f args0 args s0 s,
 KRel j w K0 K -> VRel j w f0 f -> Forall2 (VRel j w) args0 args -> SRel j w s0 s ->
 ObsT j w (Cfg (Ret f0) (KApply args0 :: K0) s0) (Cfg (Ret f) (KApply args :: K) s).

Lemma AppAll_of_AppAt : forall n w K0 K, (forall i, (i <= n)%nat -> AppAt i) -> KRel n w K0 K -> AppAll n w K0 K.
Proof.
 intros n w K0 K H HK i w' f0 f Li W V i' w'' args0 args s0 s Li' W' A HS.
 apply (H i' ltac:(lia)); [eapply KRel_mono; [|eapply wext_trans; [exact W|exact W']|exact HK]; lia| |exact A|exact HS].
 eapply VRel_mono; [exact Li'|exact W'|exact V].
Qed.

Lemma Forall2_VRel_unfold : forall j w l0 l, Forall2 (VBody (VRelF j) (S j) w) l0 l -> Forall2 (VRel (S j) w) l0 l.
Proof. intros j w l0 l F. eapply Forall2_impl; [|exact F]. intros a b H. rewrite VRel_unfold. exact H. Qed.

Lemma app_at_step : forall k n, fund_below k -> prim_compat_statement -> (S n <= k)%nat ->
 (forall i, (i <= n)%nat -> AppAt i) -> AppAt (S n).
Proof.
 intros k n F PC Ln IHa w K0 K f0 f args0 args s0 s HK HV HA HS.
 assert (HK' : KRel n w K0 K) by (eapply KRel_down; [|exact HK]; lia).
 assert (HS' : SRel n w s0 s) by (eapply SRel_down; [|exact HS]; lia).
 assert (HA' : Forall2 (VRel n w) args0 args) by (eapply Forall2_VRel_mono; [|apply wext_self with (k := S n) (s0 := s0) (s := s); exact HS|exact HA]; lia).
 pose proof (AppAll_of_AppAt n w K0 K IHa HK') as HAA.
 assert (Fn : fund_below (S n)) by (eapply fund_below_down; [exact Ln|exact F]).
 apply app_step; [exact HK'|exact HS'|].
 rewrite VRel_unfold in HV. change (VBody (VRelF n) (S n) w f0 f) in HV.
 destruct f0, f; try (cbn in HV; contradiction).
 all: try exact (throw_rel n w XNotCallable K0 K s0 s HK' HS').
 - (* two lambdas *)
   destruct HV as [_ Hb]. destruct HA' as [|a0 a rest0 rest Ha Hrest]; [exact (throw_rel n w XArity K0 K s0 s HK' HS')|].
   cbn [apply_value_r MoveRel]. rewrite !continue_jit.
   eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS'|apply KRel_kapp; [exact HK'|exact HAA|exact Hrest]|exact HS'].
   exact (Hb n (Nat.lt_succ_diag_r n) w (wext_self _ _ _ _ HS') a0 a Ha).
 - (* two frozen bodies *)
   destruct HV as [_ Hb]. destruct HA' as [|a0 a rest0 rest Ha Hrest]; [|exact (throw_rel n w XArity K0 K s0 s HK' HS')].
   cbn [apply_value_r MoveRel].
   eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS'|exact HK'|exact HS'].
   exact (Hb n (Nat.lt_succ_diag_r n) w (wext_self _ _ _ _ HS')).
 - (* two partial applications: a call through the function table *)
   apply VBody_partial in HV as [<- Hp].
   match goal with |- MoveRel _ _ (apply_value_r _ _ (VPartial ?g ?p0) _ _ _) (apply_value_r _ _ (VPartial _ ?p) _ _ _) =>
     refine (call_rel n w g (p0 ++ args0) (p ++ args) K0 K s0 s Fn PC HK' HAA _ HS') end.
   apply Forall2_app; [|exact HA']. eapply Forall2_VRel_mono; [|apply wext_self with (k := n) (s0 := s0) (s := s); exact HS'|].
   + apply Nat.le_succ_diag_r.
   + apply Forall2_VRel_unfold. exact Hp.
Qed.

Theorem app_at : forall k, fund_below k -> prim_compat_statement -> forall j, (j <= k)%nat -> AppAt j.
Proof.
 intros k F PC. assert (H : forall n j, (j <= n)%nat -> (j <= k)%nat -> AppAt j).
 { induction n as [|n IH]; intros j Ln Lk.
   - assert (j = 0%nat) by lia. subst. intros w K0 K f0 f args0 args s0 s _ _ _ _. apply ObsT_0.
   - destruct (Nat.eq_dec j (S n)) as [->|Ne]; [|apply IH; lia].
     apply (app_at_step k n F PC Lk). intros i Li. apply IH; lia. }
 intros j L. exact (H j j (le_n j) L).
Qed.

(* AppAll at index k for every continuation pair related there. *)
Theorem app_rel : forall k w K0 K, fund_below k -> prim_compat_statement -> KRel k w K0 K -> AppAll k w K0 K.
Proof. intros k w K0 K F PC HK. apply AppAll_of_AppAt; [|exact HK]. intros i Li. exact (app_at k F PC i Li). Qed.

(* EApp from its head and arguments related below k. *)
Theorem compat_app_core : forall k w rho0 h0 as0 rho h as1, fund_below k -> prim_compat_statement ->
 (forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 h0 rho h) ->
 Forall2 (fun a0 a => forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 a0 rho a) as0 as1 ->
 ERel k w rho0 (EApp h0 as0) rho (EApp h as1).
Proof.
 intros k w rho0 h0 as0 rho h as1 F PC Hh Has.
 apply (ERel_push k w rho0 (EApp h0 as0) rho (EApp h as1) rho0 h0 rho h
   (fun K0 => KHead as0 rho0 :: K0) (fun K => KHead as1 rho :: K)).
 - intros K0 s0. reflexivity.
 - intros K s. reflexivity.
 - intros j w' K0 K Lj W HK. apply KRel_KHead; [exact HK| |].
   + apply app_rel; [eapply fund_below_down; [|exact F]; lia|exact PC|exact HK].
   + eapply Forall2_impl; [|exact Has]. intros a0 a Ha. apply Ha; assumption.
 - exact Hh.
Qed.

Lemma fv_app_head : forall h args y, In y (fv h) -> In y (fv (EApp h args)).
Proof. intros h args y I. cbn [fv]. apply in_or_app. left. exact I. Qed.

Lemma fv_app_arg : forall h a rest y, In y (fv a) -> In y (fv (EApp h (a :: rest))).
Proof. intros h a rest y I. cbn [fv]. apply in_or_app. right. apply in_or_app. left. exact I. Qed.

Lemma fv_app_rest : forall h a rest y, In y (fv (EApp h rest)) -> In y (fv (EApp h (a :: rest))).
Proof.
 intros h a rest y I. cbn [fv] in *. apply in_app_or in I as [I|I]; apply in_or_app; [left; exact I|].
 right. apply in_or_app. right. exact I.
Qed.

Lemma FvOk_args : forall g rho0 rho h args, FvOk g rho0 rho (EApp h args) -> Forall (FvOk g rho0 rho) args.
Proof.
 intros g rho0 rho h args. induction args as [|a rest IH]; intros H; constructor.
 - intros y I. apply H. apply fv_app_arg. exact I.
 - apply IH. intros y I. apply H. apply fv_app_rest. exact I.
Qed.

(* The reflexive form JitKTermFund's induction uses, from fund_below k. *)
Theorem compat_app_lt : forall k w g rho0 rho h args, fund_below k -> prim_compat_statement -> wf_world w ->
 EnvRel_with (VRel k) w g rho0 rho -> FvOk g rho0 rho (EApp h args) ->
 ERel k w rho0 (EApp h args) rho (EApp h args).
Proof.
 intros k w g rho0 rho h args F PC Wf HE Hfv. apply compat_app_core; [exact F|exact PC| |].
 - intros j w' Lj W. apply (F j Lj w' g); [apply W|eapply EnvRel_mono; [|exact W|exact HE]; lia|].
   intros y Iy. apply Hfv. apply fv_app_head. exact Iy.
 - pose proof (FvOk_args g rho0 rho h args Hfv) as Fa. clear Hfv. induction Fa as [|a rest Ha Fa IH]; constructor; [|exact IH].
   intros j w' Lj W. apply (F j Lj w' g); [apply W|eapply EnvRel_mono; [|exact W|exact HE]; lia|exact Ha].
Qed.

(* compat_app_statement, given the fundamental property below every index and the primitives'
   compatibility. Not proved outright here: see the header. *)
Theorem compat_app_of_fund : fund_gen_statement -> prim_compat_statement -> compat_app_statement.
Proof.
 intros FG PC g h0 h as0 as1 Dwf Hh Has k w rho0 rho Wf HE. apply compat_app_core; [|exact PC| |].
 - destruct k as [|k]; [intros j Lj; lia|exact (FG Dwf k)].
 - intros j w' Lj W. apply Hh; [apply W|eapply EnvRel_mono; [|exact W|exact HE]; lia].
 - eapply Forall2_impl; [|exact Has]. intros a0 a Ha j w' Lj W. apply Ha; [apply W|].
   eapply EnvRel_mono; [|exact W|exact HE]; lia.
Qed.
End Equiv.
End JitKTermCompatClo.
