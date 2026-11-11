(* Shen/JIT Phase 2: KRef's control compatibility lemmas (kref-ctl). The statements compat_lit,
   compat_var, compat_let, compat_if, compat_and, compat_or, compat_cond, compat_type and
   compat_defun are JitKRef.v's; this file proves them. It re-opens Section Equiv with JitKRef.v's
   Variables and the abbreviations of JitKRefBase.v. No Definition here changes a JitKRef
   statement; the helper Definitions (MRel, AppExn) are used by lemma statements only.

   Structure. Each construct has an ERel-level lemma (ERel_sval, ERel_let, ERel_if, ERel_and,
   ERel_or, ERel_cond, ERel_type, ERel_trap, ERel_defun), proved from JitKRefBase's bind lemma
   (ERel_push), its frame lemmas (KRel_KLet, KRel_KIf, KRel_KAnd, KRel_KOr, KRel_KCond, KRel_KTrap)
   and its observation lemmas (ObsT_running, ObsT_step, wrong_match). ERel_let's body hypothesis
   is at every j <= k, under every world extending w, for VRel-related bound values: exactly
   KRel_KLet's premise. The KRef-level statements follow by relating the environments
   (env_cons for a let binder).

   - compat_defun: both sides take the same branch (jit_rules' defun_allowed ignores the store),
     add the same entry to gfuns, and return the same symbol. StoreHas of the new store is
     storehas_stable (JitKRefBase), which rests on sealed_step: D_wf puts every D name in sealed,
     and defun refuses a sealed name.
   - trap. The handler is applied to the exception through KTrap's throw_move and KApply. Applying
     a VRel-related function value to (VExn x) (AppExn) needs: for a lambda, VBody's own clause;
     for a partial application of a user function, the fundamental property one index lower
     (fund_below k: the callee's body against itself, its free variables outside the parameters
     unbound on both sides); for a partial application of a PRIMITIVE, prim_compat_statement,
     because a handler may be (VPartial "+" [1]) or any other partial primitive, and applying it
     runs prim_rule_r. So compat_trap_lt takes BOTH fund_below k and prim_compat_statement, and
     compat_trap_of_fund derives compat_trap_statement from prim_compat_statement and
     fund_gen_statement. The direct route from fund_below k alone, without a proof of the
     primitives, is obstructed (an informal index count, not a Rocq counterexample): ObsT pays one
     index per target step. In AppExn_of at index S j <= k, the primitive case needs PoutRel j of
     the outcome; fund_below k relates the Eval config of a call such as (ECall p [EVar y1; ...])
     at most at j, and that config reaches prim_rule_r only after a target step, so it relates the
     outcome at j - 1 at best. JitKRefPrim proves prim_compat_statement with no hypothesis
     (prim_compat), so the fund_below-only forms are corollaries: AppExn_fb (AppExn k from
     fund_below k), compat_trap_fb (compat_trap_lt prim_compat) and compat_trap_of_gen
     (compat_trap_statement from fund_gen_statement alone). JitKRefCompatClo's app_rel and
     compat_app_of_fund take the same two premises for the same reason.

   Does NOT prove: compat_lambda, freeze, app, call (JitKRefCompatClo), prim_compat_statement
   (JitKRefPrim; used here, not proved here), fund_gen_statement, the fundamental property or
   compat_trap_statement unconditionally (JitKRefFund). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefPrim.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefCompatCtl.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKRef.JitKRef
 JitKRefGround.JitKRefGround JitKRefBase.JitKRefBase.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
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
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).
Notation fund_gen_statement := (JitKRef.JitKRef.fund_gen_statement sealed D).
Notation PoutRel := (JitKRef.JitKRef.PoutRel sealed D).
Notation PrimOutRel := (JitKRef.JitKRef.PrimOutRel sealed D).
Notation prim_compat_statement := (JitKRef.JitKRef.prim_compat_statement sealed D).
Notation compat_lit_statement := (JitKRef.JitKRef.compat_lit_statement sealed D).
Notation compat_var_statement := (JitKRef.JitKRef.compat_var_statement sealed D).
Notation compat_let_statement := (JitKRef.JitKRef.compat_let_statement sealed D).
Notation compat_if_statement := (JitKRef.JitKRef.compat_if_statement sealed D).
Notation compat_and_statement := (JitKRef.JitKRef.compat_and_statement sealed D).
Notation compat_or_statement := (JitKRef.JitKRef.compat_or_statement sealed D).
Notation compat_cond_statement := (JitKRef.JitKRef.compat_cond_statement sealed D).
Notation compat_type_statement := (JitKRef.JitKRef.compat_type_statement sealed D).
Notation compat_trap_statement := (JitKRef.JitKRef.compat_trap_statement sealed D).
Notation compat_defun_statement := (JitKRef.JitKRef.compat_defun_statement sealed D).
Notation VRel_unfold := (JitKRefGround.JitKRefGround.VRel_unfold sealed D).
Notation ERel_iff := (JitKRefBase.JitKRefBase.ERel_iff sealed D).
Notation storehas_stable := (JitKRefBase.JitKRefBase.storehas_stable sealed D).
Notation jit_port_prim_none := (JitKRefBase.JitKRefBase.jit_port_prim_none sealed).

(* ======================= moves ======================= *)
(* Two next moves that are related: both silent, to observably related configurations, or the
   same IO request with observably related continuations for every response. *)
Definition MRel (j : nat) (w : world) (m0 m : move) : Prop :=
 match m0, m with
 | MTau c0, MTau c => ObsT j w c0 c
 | MIO q0 k0, MIO q k => q0 = q /\ forall r, ObsT j w (k0 r) (k r)
 | _, _ => False end.

Lemma srun_io : forall c q kk r, next_r R P c = MIO q kk -> srun c [EvIO q r] (kk r).
Proof.
 intros c q kk r E. unfold JitKRef.JitKRef.srun.
 change [EvIO q r] with (trace_of (Obs (EvIO q r)) ++ []). econstructor; [apply step_r_io; exact E|constructor].
Qed.

(* A running source whose next move is related to the target's, and whose Throw configurations
   are related (for the target's resource steps), is observably related one index up. *)
Theorem ObsT_of_MRel : forall j w c0 c, running_state c0 = true ->
 (forall x, ObsT j w (Cfg (Throw x) (kont c0) (mem c0)) (Cfg (Throw x) (kont c) (mem c))) ->
 MRel j w (next_r R P c0) (next_r R P c) -> ObsT (S j) w c0 c.
Proof.
 intros j w c0 c Rs Hx M. apply ObsT_running; [exact Rs| |exact Hx| |].
 - unfold nonterm. destruct (next_r R P c) eqn:E; destruct (next_r R P c0); cbn in M; try contradiction; exact I.
 - intros c1 E. rewrite E in M. destruct (next_r R P c0) eqn:E0; cbn in M; try contradiction.
   exists c2. split; [eapply srun_tau; [exact E0|apply srun_refl]|exact M].
 - intros q kk r E. rewrite E in M. destruct (next_r R P c0) eqn:E0; cbn in M; try contradiction.
   destruct M as [<- M]. exists (k r). split; [apply srun_io; exact E0|apply M].
Qed.

(* ======================= values and exceptions in one step ======================= *)
(* A literal, or a bound variable, on each side: one silent step to related values. *)
Theorem ERel_sval : forall k w rho0 e0 rho e v0 v, sval rho0 e0 = Some v0 -> sval rho e = Some v ->
 VRel k w v0 v -> ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e v0 v E0 E HV. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|]. apply ObsT_of_MRel; [reflexivity| |].
 - intros x. cbn [kont mem]. eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - rewrite (sval_next _ _ _ _ _ _ E0), (sval_next _ _ _ _ _ _ E). cbn [MRel].
   eapply KRel_ret; [eapply KRel_down; [|exact HK]; lia|eapply VRel_mono; [|exact W|exact HV]; lia|eapply SRel_down; [|exact HS]; lia].
Qed.

(* Both sides raise the same exception in one silent step. *)
Theorem ERel_throw_both : forall k w rho0 e0 rho e x,
 (forall K0 s0, next_r R P (Cfg (Eval rho0 e0) K0 s0) = MTau (Cfg (Throw x) K0 s0)) ->
 (forall K s, next_r R P (Cfg (Eval rho e) K s) = MTau (Cfg (Throw x) K s)) ->
 ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e x E0 E. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|]. apply ObsT_of_MRel; [reflexivity| |].
 - intros y. cbn [kont mem]. eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - rewrite E0, E. cbn [MRel].
   eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
Qed.

Lemma lit_sval : forall rho e v, lit_val e = Some v -> sval rho e = Some v.
Proof. intros rho e v H. destruct e; cbn in H |- *; try discriminate; exact H. Qed.

Lemma VRel_lit : forall k w e v, lit_val e = Some v -> VRel k w v v.
Proof.
 intros k w e v H. destruct e; cbn in H; try discriminate; injection H as <-; rewrite (VRel_unfold k); reflexivity.
Qed.

(* ======================= compound forms: the bind lemma ======================= *)
Theorem ERel_let : forall k w x0 a0 b0 rho0 x a b rho, ERel k w rho0 a0 rho a ->
 (forall j w' v0 v, (j <= k)%nat -> wext w w' -> VRel j w' v0 v -> ERel j w' ((x0, v0) :: rho0) b0 ((x, v) :: rho) b) ->
 ERel k w rho0 (ELet x0 a0 b0) rho (ELet x a b).
Proof.
 intros k w x0 a0 b0 rho0 x a b rho Ha Hb.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a)
   (F0 := fun K => KLet x0 b0 rho0 :: K) (F := fun K => KLet x b rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. apply KRel_KLet; [exact HK|].
   intros j' w'' v0 v L' W' HV. apply Hb; [lia|eapply wext_trans; eauto|exact HV].
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.

Theorem ERel_if : forall k w c0 a0 b0 rho0 c a b rho, ERel k w rho0 c0 rho c -> ERel k w rho0 a0 rho a ->
 ERel k w rho0 b0 rho b -> ERel k w rho0 (EIf c0 a0 b0) rho (EIf c a b).
Proof.
 intros k w c0 a0 b0 rho0 c a b rho Hc Ha Hb.
 eapply ERel_push with (rho0' := rho0) (e0' := c0) (rho' := rho) (e' := c)
   (F0 := fun K => KIf a0 b0 rho0 :: K) (F := fun K => KIf a b rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. apply KRel_KIf; [exact HK| |]; (eapply ERel_mono; [|exact W|eassumption]; lia).
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Hc]; lia.
Qed.

Theorem ERel_and : forall k w a0 b0 rho0 a b rho, ERel k w rho0 a0 rho a -> ERel k w rho0 b0 rho b ->
 ERel k w rho0 (EAnd a0 b0) rho (EAnd a b).
Proof.
 intros k w a0 b0 rho0 a b rho Ha Hb.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a)
   (F0 := fun K => KAnd b0 rho0 :: K) (F := fun K => KAnd b rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. apply KRel_KAnd; [exact HK|]. eapply ERel_mono; [|exact W|exact Hb]; lia.
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.

Theorem ERel_or : forall k w a0 b0 rho0 a b rho, ERel k w rho0 a0 rho a -> ERel k w rho0 b0 rho b ->
 ERel k w rho0 (EOr a0 b0) rho (EOr a b).
Proof.
 intros k w a0 b0 rho0 a b rho Ha Hb.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a)
   (F0 := fun K => KOr b0 rho0 :: K) (F := fun K => KOr b rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. apply KRel_KOr; [exact HK|]. eapply ERel_mono; [|exact W|exact Hb]; lia.
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.

(* type is a silent step to its operand on both sides: the bind lemma with no frame. *)
Theorem ERel_type : forall k w a0 rho0 a rho, ERel k w rho0 a0 rho a -> ERel k w rho0 (EType a0) rho (EType a).
Proof.
 intros k w a0 rho0 a rho Ha.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a) (F0 := fun K => K) (F := fun K => K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. exact HK.
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.

(* cond, clause by clause in order: an empty cond raises XCondFail on both sides. *)
Theorem ERel_cond : forall cl0 cl k w rho0 rho,
 Forall2 (fun p0 p => ERel k w rho0 (fst p0) rho (fst p) /\ ERel k w rho0 (snd p0) rho (snd p)) cl0 cl ->
 ERel k w rho0 (ECond cl0) rho (ECond cl).
Proof.
 induction cl0 as [|[c0 b0] cl0 IH]; intros cl k w rho0 rho F; inversion F as [|p0 p l0 l Hp Fr]; subst.
 - apply (ERel_throw_both _ _ _ _ _ _ XCondFail); intros; reflexivity.
 - destruct p as [c b]. cbn [fst snd] in Hp. destruct Hp as [Hc Hb]. pose proof (IH l k w rho0 rho Fr) as Hr.
   eapply ERel_push with (rho0' := rho0) (e0' := c0) (rho' := rho) (e' := c)
     (F0 := fun K => KCond b0 cl0 rho0 :: K) (F := fun K => KCond b l rho :: K).
   + intros; reflexivity.
   + intros; reflexivity.
   + intros j w' K0 K L W HK. apply KRel_KCond; [exact HK| |]; (eapply ERel_mono; [|exact W|eassumption]; lia).
   + intros j w' L W. eapply ERel_mono; [|exact W|exact Hc]; lia.
Qed.

(* ======================= defun ======================= *)
Lemma next_defun : forall rho f ps b K s,
 next_r R P (Cfg (Eval rho (EDefun f ps b)) K s) =
 if defun_allowed R s f then if nodupb ps then
   MTau (Cfg (Ret (VSym f)) K (Store (heap s) (gvals s) ((f, FUser ps b) :: gfuns s)))
   else MTau (Cfg (Throw XBadDefinition) K s)
 else MTau (Cfg (Throw XBadDefinition) K s).
Proof. reflexivity. Qed.

(* A defun on both sides of related stores: the same entry added to equal function tables. The
   new stores still meet D by storehas_stable, which needs D_wf. *)
Theorem ERel_defun : D_wf -> forall k w rho0 rho f ps b, ERel k w rho0 (EDefun f ps b) rho (EDefun f ps b).
Proof.
 intros Dw k w rho0 rho f ps b. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|]. apply ObsT_of_MRel; [reflexivity| |].
 - intros y. cbn [kont mem]. eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - pose proof (next_defun rho0 f ps b K0 s0) as E0. pose proof (next_defun rho f ps b K s) as E.
   change (defun_allowed R s0 f) with (defun_allowed R s f) in E0.
   rewrite E0, E. destruct (defun_allowed R s f) eqn:A; [destruct (nodupb ps) eqn:N|]; cbn [MRel].
   2, 3: eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
   eapply KRel_ret; [eapply KRel_down; [|exact HK]; lia|rewrite (VRel_unfold j); reflexivity|].
   apply (SRel_down sealed D (S j)); [lia|]. destruct HS as (Wf & H0 & H1 & G & Gv & Hp).
   split; [exact Wf|split; [|split; [|split; [cbn; rewrite G; reflexivity|split; [exact Gv|exact Hp]]]]].
   + apply (storehas_stable (Cfg (Eval rho0 (EDefun f ps b)) K0 s0) []
       (Cfg (Ret (VSym f)) K0 (Store (heap s0) (gvals s0) ((f, FUser ps b) :: gfuns s0)))); [exact Dw| |exact H0].
     eapply srun_tau; [rewrite next_defun; change (defun_allowed R s0 f) with (defun_allowed R s f); rewrite A, N; reflexivity|].
     apply srun_refl.
   + apply (storehas_stable (Cfg (Eval rho (EDefun f ps b)) K s) []
       (Cfg (Ret (VSym f)) K (Store (heap s) (gvals s) ((f, FUser ps b) :: gfuns s)))); [exact Dw| |exact H1].
     eapply srun_tau; [rewrite next_defun, A, N; reflexivity|]. apply srun_refl.
Qed.

(* ======================= trap: applying the handler to the exception ======================= *)
(* Applying related function values to one exception, under related continuations and stores,
   at every index up to k. *)
Definition AppExn (k : nat) : Prop :=
 forall j w K0 K x f0 f s0 s, (j <= k)%nat -> KRel j w K0 K -> VRel j w f0 f -> SRel j w s0 s ->
  ObsT j w (Cfg (Ret f0) (KApply [VExn x] :: K0) s0) (Cfg (Ret f) (KApply [VExn x] :: K) s).

Theorem KRel_KApply_exn : forall k j w K0 K x, AppExn k -> (j <= k)%nat -> KRel j w K0 K ->
 KRel j w (KApply [VExn x] :: K0) (KApply [VExn x] :: K).
Proof.
 intros k j w K0 K x HA L HK. apply KRel_push; [exact HK|reflexivity|reflexivity|].
 intros j' w' v0 v s0 s L' W HV HS. apply HA; [lia|eapply KRel_mono; [exact L'|exact W|exact HK]|exact HV|exact HS].
Qed.

Theorem ERel_trap : forall k w a0 h0 rho0 a h rho, AppExn k -> ERel k w rho0 a0 rho a -> ERel k w rho0 h0 rho h ->
 ERel k w rho0 (ETrap a0 h0) rho (ETrap a h).
Proof.
 intros k w a0 h0 rho0 a h rho HA Ha Hh.
 eapply ERel_push with (rho0' := rho0) (e0' := a0) (rho' := rho) (e' := a)
   (F0 := fun K => KTrap h0 rho0 :: K) (F := fun K => KTrap h rho :: K).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j w' K0 K L W HK. apply KRel_KTrap; [exact HK|eapply ERel_mono; [|exact W|exact Hh]; lia|].
   intros x. eapply KRel_KApply_exn; [exact HA|lia|exact HK].
 - intros j w' L W. eapply ERel_mono; [|exact W|exact Ha]; lia.
Qed.

(* ---------- environments of a call ---------- *)
Lemma lookup_combine_notin : forall {A} y ps (l : list A), ~ In y ps -> lookup y (combine ps l) = None.
Proof.
 intros A y ps. induction ps as [|p ps IH]; intros [|a l] N; cbn; try reflexivity.
 destruct (text_eqb y p) eqn:E; [apply text_eqb_eq in E; subst; exfalso; apply N; left; reflexivity|].
 apply IH. intros I; apply N; right; exact I.
Qed.

Lemma env_combine : forall j w ps args0 args, Forall2 (VRel j w) args0 args -> List.length ps = List.length args ->
 EnvRel_with (VRel j) w ps (combine ps args0) (combine ps args).
Proof.
 intros j w ps. induction ps as [|p ps IH]; intros args0 args F L y I; [destruct I|].
 destruct F as [|a0 a args0 args Ha F]; [discriminate|]. cbn in L. injection L as L. cbn [combine lookup].
 destruct (text_eqb y p) eqn:E; [exists a0, a; auto|].
 destruct I as [<-|I]; [rewrite text_eqb_refl in E; discriminate|]. exact (IH args0 args F L y I).
Qed.

Lemma env_cons : forall j w g x rho0 rho v0 v, EnvRel_with (VRel j) w g rho0 rho -> VRel j w v0 v ->
 EnvRel_with (VRel j) w (x :: g) ((x, v0) :: rho0) ((x, v) :: rho).
Proof.
 intros j w g x rho0 rho v0 v HE HV y I. cbn [lookup]. destruct (text_eqb y x) eqn:E; [exists v0, v; auto|].
 destruct I as [<-|I]; [rewrite text_eqb_refl in E; discriminate|]. exact (HE y I).
Qed.

(* ---------- primitive outcomes ---------- *)
Lemma ObsT_fail : forall j w r K0 K s0 s, KRel j w K0 K -> SRel j w s0 s ->
 ObsT j w (Cfg (Fail r) K0 s0) (Cfg (Fail r) K s).
Proof.
 intros j w r K0 K s0 s HK HS. destruct j as [|j]; [apply ObsT_0|].
 assert (Rx : exists x, resource_exn R r = Some x) by (destruct r; eexists; reflexivity). destruct Rx as [x Rx].
 assert (Ef : forall K1 s1, next_r R P (Cfg (Fail r) K1 s1) = MTau (Cfg (Throw x) K1 s1))
   by (intros; cbn [next_r ctl kont mem]; rewrite Rx; reflexivity).
 apply ObsT_step.
 - unfold nonterm. rewrite Ef. exact I.
 - intros l c1 St. destruct (step_r_cases _ _ _ _ St) as [[E ->]|[(q & kk & r' & E & _)|(r' & y & Rc & _)]].
   + rewrite Ef in E. injection E as <-. apply (ObsT_anti_io _ _ _ [] _ (Cfg (Throw x) K0 s0)).
     * eapply srun_tau; [apply Ef|apply srun_refl].
     * eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
   + rewrite Ef in E. discriminate.
   + cbn in Rc. discriminate.
Qed.

Lemma pout_obs : forall k j w o0 o K0 K s0 s, fund_below k -> (j < k)%nat -> KRel j w K0 K -> SRel j w s0 s ->
 PoutRel j w o0 o -> ObsT j w (pout_config P o0 [] K0 s0) (pout_config P o [] K s).
Proof.
 intros k j w o0 o K0 K s0 s Hf L HK HS H. destruct o0, o; cbn in H; try contradiction; cbn [pout_config continue_with].
 - destruct H as (w' & W & HV & HS'). eapply ObsT_wext_anti; [exact W|].
   eapply KRel_ret; [eapply KRel_wext; [exact W|exact HK]|exact HV|exact HS'].
 - subst. eapply KRel_throw; eassumption.
 - subst. eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS|exact HK|exact HS].
   apply (Hf j L w [] [] []); [eapply SRel_wf; exact HS|intros y []|intros y _; right; split; reflexivity].
 - subst. apply ObsT_fail; assumption.
 - eapply wrong_match; [reflexivity|]. do 2 eexists. split; [apply srun_refl|reflexivity].
Qed.

(* ---------- application to one exception ---------- *)
Lemma Forall2_VBody_VRel : forall j w l0 l, Forall2 (VBody (VRelF j) (S j) w) l0 l -> Forall2 (VRel (S j) w) l0 l.
Proof. intros j w l0 l F. rewrite (VRel_unfold (S j)). exact F. Qed.

Lemma arity_ok : forall n m, arity_mismatch R n m = false -> n = m.
Proof.
 intros n m H. unfold arity_mismatch in H. change (arity_errors R) with true in H. cbn [andb] in H.
 apply Bool.negb_false_iff, Nat.eqb_eq in H. exact H.
Qed.

(* A handler applied to the exception. A lambda by its VBody clause, at one index less; a partial
   application of a user function by the callee's body against itself (fund_below); of a
   primitive by prim_compat_statement; anything else raises the same exception on both sides. *)
Theorem AppExn_of : prim_compat_statement -> forall k, fund_below k -> AppExn k.
Proof.
 intros Hp k Hf j w K0 K x f0 f s0 s L HK HV HS. destruct j as [|j]; [apply ObsT_0|].
 assert (Thr : forall y, ObsT j w (Cfg (Throw y) K0 s0) (Cfg (Throw y) K s))
   by (intros y; eapply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia]).
 assert (HKj : KRel j w K0 K) by (eapply KRel_down; [|exact HK]; lia).
 assert (HSj : SRel j w s0 s) by (eapply SRel_down; [|exact HS]; lia).
 apply ObsT_of_MRel; [reflexivity| |].
 { intros y. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|reflexivity|reflexivity|lia|eapply wext_self; exact HS|exact HSj]. }
 change (MRel j w (apply_value_r R P f0 [VExn x] K0 s0) (apply_value_r R P f [VExn x] K s)).
 pose proof HV as HB. rewrite (VRel_unfold (S j)) in HB.
 destruct f0, f; cbn in HB; try contradiction; cbn [apply_value_r continue_with MRel]; try apply Thr.
 - (* lambdas *)
   destruct HB as [_ HB]. eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS|exact HKj|exact HSj].
   apply (HB j (le_n (S j)) w (wext_self _ _ _ _ _ _ HS) (VExn x) (VExn x)).
   change (VRel j w (VExn x) (VExn x)). rewrite (VRel_unfold j). reflexivity.
 - (* partial applications *)
   apply VBody_partial in HB as [<- Fa]. apply Forall2_VBody_VRel in Fa.
   match goal with |- context [call_named_r _ _ ?g _ _ _] => rename g into gn end.
   assert (Fs : Forall2 (VRel (S j) w) (args ++ [VExn x]) (args0 ++ [VExn x])).
   { apply Forall2_app; [exact Fa|constructor; [rewrite (VRel_unfold (S j)); reflexivity|constructor]]. }
   assert (Fj : Forall2 (VRel j w) (args ++ [VExn x]) (args0 ++ [VExn x])) by (eapply Forall2_VRel_mono; [|eapply wext_self; exact HS|exact Fs]; lia).
   pose proof (Forall2_length Fs) as Ln.
   assert (G : gfuns s0 = gfuns s) by (destruct HS as (_ & _ & _ & G & _); exact G).
   unfold call_named_r. rewrite G. destruct (lookup gn (gfuns s)) as [[p|ps body]|].
   + (* a primitive *)
     rewrite Ln. destruct (arity_mismatch R (List.length (args0 ++ [VExn x])) (prim_arity p)) eqn:A; cbn [MRel]; [apply Thr|].
     apply arity_ok in A. rewrite A, Nat.ltb_irrefl. rewrite !firstn_all2, !skipn_all2 by lia.
     unfold prim_move_r. pose proof (proj1 (Hp j w) p _ _ s0 s Fj HSj) as Hr.
     destruct (prim_rule_r R P p (args ++ [VExn x]) s0), (prim_rule_r R P p (args0 ++ [VExn x]) s);
      cbn in Hr; try contradiction; cbn [MRel].
     * eapply pout_obs; [exact Hf|lia|exact HKj|exact HSj|exact Hr].
     * destruct Hr as [<- Hr]. split; [reflexivity|]. intros r.
       eapply pout_obs; [exact Hf|lia|exact HKj|exact HSj|apply Hr].
   + (* a user function *)
     rewrite Ln. destruct (arity_mismatch R (List.length (args0 ++ [VExn x])) (List.length ps)) eqn:A; cbn [MRel]; [apply Thr|].
     apply arity_ok in A. rewrite A, Nat.ltb_irrefl. rewrite !firstn_all2, !skipn_all2 by lia. cbn [MRel].
     cbn [continue_with]. eapply ERel_apply; [|apply le_n|eapply wext_self; exact HS|exact HKj|exact HSj].
     apply (Hf j ltac:(lia) w ps); [eapply SRel_wf; exact HS|apply env_combine; [exact Fj|lia]|].
     intros y _. destruct (in_dec (list_eq_dec N.eq_dec) y ps) as [I|I]; [left; exact I|right].
     split; apply lookup_combine_notin; exact I.
   + (* undefined *)
     rewrite jit_port_prim_none. cbn [MRel]. apply Thr.
Qed.

(* ======================= the KRef statements ======================= *)
Theorem compat_lit : compat_lit_statement.
Proof.
 intros g e v H k w rho0 rho Ww HE. eapply ERel_sval; [apply lit_sval; exact H|apply lit_sval; exact H|].
 eapply VRel_lit; exact H.
Qed.

Theorem compat_var : compat_var_statement.
Proof.
 intros g x I k w rho0 rho Ww HE. destruct (HE x I) as (v0 & v & E0 & E & HV).
 eapply ERel_sval; [exact E0|exact E|exact HV].
Qed.

Theorem compat_let : compat_let_statement.
Proof.
 intros g x a0 a b0 b Ha Hb k w rho0 rho Ww HE. apply ERel_let; [apply Ha; assumption|].
 intros j w' v0 v L W HV. apply Hb; [apply W|]. apply env_cons; [eapply EnvRel_mono; eauto|exact HV].
Qed.

Theorem compat_if : compat_if_statement.
Proof.
 intros g c0 c a0 a b0 b Hc Ha Hb k w rho0 rho Ww HE.
 apply ERel_if; [apply Hc|apply Ha|apply Hb]; assumption.
Qed.

Theorem compat_and : compat_and_statement.
Proof. intros g a0 a b0 b Ha Hb k w rho0 rho Ww HE. apply ERel_and; [apply Ha|apply Hb]; assumption. Qed.

Theorem compat_or : compat_or_statement.
Proof. intros g a0 a b0 b Ha Hb k w rho0 rho Ww HE. apply ERel_or; [apply Ha|apply Hb]; assumption. Qed.

Theorem compat_cond : compat_cond_statement.
Proof.
 intros g cl0 cl F k w rho0 rho Ww HE. apply ERel_cond.
 eapply Forall2_impl; [|exact F]. intros p0 p [H1 H2]. split; [apply H1|apply H2]; assumption.
Qed.

Theorem compat_type : compat_type_statement.
Proof. intros g a0 a Ha k w rho0 rho Ww HE. apply ERel_type. apply Ha; assumption. Qed.

Theorem compat_defun : compat_defun_statement.
Proof. intros g f ps b Dw k w rho0 rho Ww HE. apply ERel_defun. exact Dw. Qed.

(* trap at index k, from the fundamental property below k AND prim_compat_statement (see the
   header: a partial primitive is a handler). *)
Theorem compat_trap_lt : prim_compat_statement -> forall k, fund_below k ->
 forall g a0 a h0 h, KRef g a0 a -> KRef g h0 h ->
 forall w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 (ETrap a0 h0) rho (ETrap a h).
Proof.
 intros Hp k Hf g a0 a h0 h Ha Hh w rho0 rho Ww HE.
 apply ERel_trap; [apply AppExn_of; assumption|apply Ha; assumption|apply Hh; assumption].
Qed.

Lemma fund_below_down : forall k j, (j <= k)%nat -> fund_below k -> fund_below j.
Proof. intros k j L H i Li. apply H. lia. Qed.

(* compat_trap_statement as an implication from the two statements kref-prim and kref-fund own. *)
Theorem compat_trap_of_fund : prim_compat_statement -> fund_gen_statement -> compat_trap_statement.
Proof.
 intros Hp Hg g a0 a h0 h Dw Ha Hh k w rho0 rho Ww HE.
 assert (Hf : fund_below k) by (apply (fund_below_down (S k)); [lia|apply Hg; exact Dw]).
 exact (compat_trap_lt Hp k Hf g a0 a h0 h Ha Hh w rho0 rho Ww HE).
Qed.

(* ======================= trap from fund_below alone ======================= *)
(* JitKRefPrim proves prim_compat_statement with no hypothesis (prim_compat), so the primitive
   premise of AppExn_of and compat_trap_lt is discharged: applying a handler to an exception, and
   trap at index k, need fund_below k only. *)
Theorem AppExn_fb : forall k, fund_below k -> AppExn k.
Proof. intros k Hf. exact (AppExn_of (JitKRefPrim.JitKRefPrim.prim_compat sealed D) k Hf). Qed.

Theorem compat_trap_fb : forall k, fund_below k ->
 forall g a0 a h0 h, KRef g a0 a -> KRef g h0 h ->
 forall w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 (ETrap a0 h0) rho (ETrap a h).
Proof. intros k. exact (compat_trap_lt (JitKRefPrim.JitKRefPrim.prim_compat sealed D) k). Qed.

(* compat_trap_statement from fund_gen_statement alone (kref-fund owns fund_gen_statement). *)
Theorem compat_trap_of_gen : fund_gen_statement -> compat_trap_statement.
Proof. exact (compat_trap_of_fund (JitKRefPrim.JitKRefPrim.prim_compat sealed D)). Qed.
End Equiv.
End JitKRefCompatCtl.
