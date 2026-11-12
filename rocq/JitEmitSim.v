(* Shen/JIT Phase 2, emit-sim (task r22-emit-sim): the generic parts of the extended back end's
   correctness statements (JitEmitInv), as implications between statements, every one closed.
   NOTHING here is assumed or Admitted; each theorem takes the statements it uses as explicit
   arguments, so Print Assumptions shows no axiom.

   FALSE as stated by r22-emit-sim (closed, at JitEmitInv.cx_E, cx_pt, sealed []): the text now
   named preservation'_statement_v1, call_preservation'_statement_v1,
   call_preservation_src'_statement_v1 (JitEmitInv) and raise_resolve_statement_v1 (here), over
   SMs_v1, which did not keep the allocation pointer m_next fresh (preservation'_false,
   call_preservation'_false, call_preservation_src'_false, raise_resolve_false); see the section
   "the statements are FALSE as stated".
   Repaired by r21-sms-fresh-fix: SMs asks sm_fresh (JitEmitInv.Fresh), so SM, MS', Ends',
   EndsSrc' and the statements over them keep m_next fresh. preservation'_statement,
   call_preservation'_statement, call_preservation_src'_statement and raise_resolve_statement
   are the corrected statements (their text unchanged, over the corrected SMs); the implications
   below are proved against them. fx_not_sm: the counterexample's machine is related by no SM.
   fresh_needed: it still meets the old statements' premises, so the corrected src statement
   reaches the old fragment only with Fresh m added (call_preservation_src_old_of_cp' targets
   JitEmitInv.call_preservation_src_old_fresh_statement), NOT the byte-identical
   JitKRef.call_preservation_src_statement. Truth of the corrected statements: UNKNOWN (not
   refuted; not proved).

   Proved here (closed):
   - MEnv_bind', entered_ms': the configuration a call enters is MS'-related (cv = [], the
     parameters in slots 2 up, the empty continuation through KC'_ret and RK'_top).
   - call_preservation'_of_preservation': preservation'_statement -> call_preservation'_statement.
   - vrh_refl: a value VRh relates (under a mu whose cells the store has) is VRel-related to itself
     at every index and every world extending the identity on the store, GIVEN clo_scoped_statement
     (a closure body that CloOK accepts is scoped in its parameters and capture names).
   - adequacy_tr: JitKRef's adequacy for any IO trace and for environments whose values are
     VRel-reflexive (JitKRefGround.adequacy_of_fundamental asks first-order values and silent runs).
   - call_preservation_src'_of_cp': call_preservation'_statement -> clo_scoped_statement ->
     call_preservation_src'_statement, through two adequacy links composed with GVal_trans and
     GStore_trans (no KRef transitivity).
   - call_preservation_src_old_of_cp': the old-fragment corollary (JitKRef's
     call_preservation_src_statement at mu = [], with GvalsRel [] s m added), from
     call_preservation'_statement, clo_scoped_statement and old_reflect'_statement.
   - preservation'_of_sim': sim'_statement -> raise_resolve_statement -> preservation'_statement,
     the many-step theorem from the one-step one (an induction on n, inside it on the source's
     measure, IO events through env_ok shifted along the environment).
   - entered_ms'_v1, call_preservation'_of_preservation'_v1: the same over the v1 relation, for
     the refutations.
   - fx_not_sm, fx_comp_old, fresh_needed (r21-sms-fresh-fix): see "after the repair".
   - the slot-1 witnesses (evalctx_slot1_void, ms'_slot1_frame): why the generic one-step proof
     (sim'_of_sims) does NOT go through on JitEmitKont's frames as stated; see there.

   NOT proved, and why (each is a named statement in JitEmitInv or here):
   - sim'_statement from the seven sim_X_statement: blocked twice in the generic Ret cases.
     (1) slot 1: EvalCtx asks (cv = [] \/ ~ w (fp + 1)) of the w its KC' is at, and no frame of
     JitEmitKont carries that for its inner w1 (KD'_let, KD'_lett, KD'_trap, KD'_do1, KD'_do1t,
     KD'_hbind, TK'_if, TK'_cond, TK'_and, TK'_or): when the frame's body writes slot 1 (DSlot 1),
     KC'_slot needs w1 (fp + 1), so no EvalCtx at that code's cv <> [] exists (evalctx_slot1_void)
     although the MS'_ret state does (ms'_slot1_frame). A generic proof cannot re-relate the state
     at another cv (it would need Comp at cv = [], which family hooks may not give).
     (2) KD'_hbind: the machine is at Comp of (chain (EVar x) ass), an EApp that only the App hook
     derives, while the source is past its Eval, at Ret with KHead frames over rho (not
     (x, v) :: rho); sim_App_statement speaks of Eval states only.
   - raise_resolve_statement (the handler half needs the same slot-1 protection, KD'_trap).
   - clo_scoped_statement: per family (the Clo hook's capture reads), through Comp_ind'.
   - the instantiation at the families' proved sim_X (emit-assembly; the hooks are empty and may
     not be inverted outside their files).
   - env_ok necessity for call_preservation' and call_preservation_src': with the hooks empty no
     Comp rule reaches an IO primitive (C_prim goes through pmap), so nothing a call enters asks
     for IO; the analogue of JitEmitInv.env_ok_needed needs a family rule reaching get-time.
   - old_reflect_core_statement: truth UNKNOWN (JitEmitInv.old_reflect'_iff_core). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation JitEmitKont KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile
 JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefCompose JitKRefFund
 JitEmitRel JitEmitInv.
Import ListNotations.
Module JitEmitSim.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitEmitRel.JitEmitRel JitEmitKont.JitEmitKont JitEmitInv.JitEmitInv.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* ---------- the entry state ---------- *)
Lemma MEnv_bind' : forall (V : value -> B.val -> Prop) ps args f s0 i, List.length ps = List.length args ->
 ArgsAt' V s0 (f + i) args -> MEnv' V f s0 [] [] (bind ps i) (combine ps args).
Proof.
 intros V. induction ps as [|p ps IH]; intros args f s0 i L A; split.
 - intros x s K; discriminate.
 - intros j x Nj; destruct j; discriminate.
 - intros x s K. destruct args as [|a args]; [discriminate|]. inversion A; subst. cbn in K |- *.
   destruct (text_eqb x p).
   + inversion K; subst. eauto.
   + refine (proj1 (IH args f s0 (i + 1) _ _) x s K); [cbn in L; lia|].
     replace (f + (i + 1)) with (f + i + 1) by lia. assumption.
 - intros j x Nj; destruct j; discriminate.
Qed.

Section Gen.
Variables (E : B.env) (pt : B.tree (B.prim * nat)) (sealed : list name).

(* The configuration a call enters is MS'-related: the old ms_entered, over SM and entered'. *)
Lemma entered_ms' : forall mu s m c ps b args, SM mu s [] m -> CompFn' c ps b -> List.length ps = List.length args ->
 entered' mu m c args -> MS' mu (Cfg (Eval (combine ps args) b) [] s) m.
Proof.
 intros mu s m c ps b args Sm [r' Cf] L (Hc & Hr & Hk & Hh & Aa).
 eapply MS'_eval with (cv := []) (caps := []) (g := bind ps 2) (top := (2 + N.of_nat (List.length ps))%N)
   (dst := DRet) (r2 := r') (w := fun a => (B.m_fp m + (2 + N.of_nat (List.length ps)) <= a)%N).
 - rewrite Hc, Hr. exact Cf.
 - unfold EvalCtx. split; [exact Sm|]. split; [apply MEnv_bind'; [exact L|exact Aa]|].
   split; [apply bind_below|]. split; [intros a A; exact A|]. split; [left; reflexivity|].
   split; [left; reflexivity|]. rewrite Hk, Hh. apply KC'_ret; [intros a A; lia|constructor].
Qed.

Theorem call_preservation'_of_preservation' : preservation'_statement E pt sealed -> call_preservation'_statement E pt sealed.
Proof.
 intros Pr mu s m c ps b args n rs Eo Sm Cf L En c0.
 exact (Pr n mu c0 m rs Eo (entered_ms' mu s m c ps b args Sm Cf L En)).
Qed.

(* The same two over the relation before r21-sms-fresh-fix (JitEmitInv's *_v1), for the
   refutations below. *)
Lemma entered_ms'_v1 : forall mu s m c ps b args, SM_v1 mu s [] m -> CompFn' c ps b -> List.length ps = List.length args ->
 entered' mu m c args -> MS'_v1 mu (Cfg (Eval (combine ps args) b) [] s) m.
Proof.
 intros mu s m c ps b args Sm [r' Cf] L (Hc & Hr & Hk & Hh & Aa).
 eapply MS'_eval_v1 with (cv := []) (caps := []) (g := bind ps 2) (top := (2 + N.of_nat (List.length ps))%N)
   (dst := DRet) (r2 := r') (w := fun a => (B.m_fp m + (2 + N.of_nat (List.length ps)) <= a)%N).
 - rewrite Hc, Hr. exact Cf.
 - unfold EvalCtx_v1. split; [exact Sm|]. split; [apply MEnv_bind'; [exact L|exact Aa]|].
   split; [apply bind_below|]. split; [intros a A; exact A|]. split; [left; reflexivity|].
   split; [left; reflexivity|]. rewrite Hk, Hh. apply KC'_ret; [intros a A; lia|constructor].
Qed.

Theorem call_preservation'_of_preservation'_v1 : preservation'_statement_v1 E pt sealed -> call_preservation'_statement_v1 E pt sealed.
Proof.
 intros Pr mu s m c ps b args n rs Eo Sm Cf L En c0.
 exact (Pr n mu c0 m rs Eo (entered_ms'_v1 mu s m c ps b args Sm Cf L En)).
Qed.

(* ---------- many steps from one ---------- *)
Notation Sstar := (Sstar sealed).
Notation TStar := (TStar E pt).
Notation TPlus := (TPlus E pt).
Notation Srun := (Srun sealed).
Notation TRun := (TRun E pt).
Notation Ends' := (Ends' E pt sealed).
Notation Out' := (Out' E pt sealed).

(* What O'_raise leaves open, resolved: from the raise (the machine m1 raising from m2, the source
   at Throw x with the continuation k that SM and one of the three frame relations relate to m2),
   either the machine steps (to the handler) and the source reaches a related state silently, or
   neither side has a handler: the machine finishes with the exception and the source throws to the
   top, the stores related.
   NOT proved here: the no-handler half needs SMs stable under the exception's allocation; the
   handler half needs the slot-1 protection at the handler (EvalCtx's (cv = [] \/ ~ w (fp + 1)))
   that KD'_trap does not carry for its inner w1 (the slot-1 gap, below).
   Does NOT say: anything about a raise whose frames are not related (O'_raise relates them). *)
Definition raise_resolve_statement : Prop := forall mu x k s m1 m2 msg tv cv caps w,
 B.next E pt m1 = B.raise m2 msg tv -> exn_ok x msg -> SM mu s k m2 ->
 CCtx (HeapClo (B.m_heap m2)) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2) ->
 ((exists o r, KD' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w o r k) \/
  (exists l r, TK' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w true l r k) \/
  (exists dst r, KC' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w dst r k)) ->
 (exists c' m' mu', Sstar (Cfg (Throw x) k s) c' /\ TPlus m1 m' /\ mext mu mu' /\ MS' mu' c' m') \/
 (exists l msg' tv' s' m3 mu', Sstar (Cfg (Throw x) k s) (Cfg (Throw x) [] s') /\
    B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m3 /\ B.tget l (B.m_heap m3) = Some (B.OExn msg' tv') /\
    exn_ok x msg' /\ mext mu mu' /\ SMs mu' s' m3).

(* raise_resolve_statement as r22-emit-sim stated it, over SM_v1, MS'_v1 and SMs_v1 (no
   sm_fresh); the text otherwise unchanged. FALSE: raise_resolve_false (below). The statement
   above is the corrected one: the same text over SM and SMs with sm_fresh. Its no-handler end is
   JitEmitInv.sms_raise_final (closed) once the raising machine is SMs-related: the exception goes
   to a fresh key. *)
Definition raise_resolve_statement_v1 : Prop := forall mu x k s m1 m2 msg tv cv caps w,
 B.next E pt m1 = B.raise m2 msg tv -> exn_ok x msg -> SM_v1 mu s k m2 ->
 CCtx (HeapClo (B.m_heap m2)) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2) ->
 ((exists o r, KD' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w o r k) \/
  (exists l r, TK' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w true l r k) \/
  (exists dst r, KC' (VRh mu (B.m_heap m2)) (HeapClo (B.m_heap m2)) (DoOK s) (B.m_code m2) cv caps (B.m_fp m2) (B.m_stack m2)
     (B.m_conts m2) (B.m_handlers m2) w dst r k)) ->
 (exists c' m' mu', Sstar (Cfg (Throw x) k s) c' /\ TPlus m1 m' /\ mext mu mu' /\ MS'_v1 mu' c' m') \/
 (exists l msg' tv' s' m3 mu', Sstar (Cfg (Throw x) k s) (Cfg (Throw x) [] s') /\
    B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m3 /\ B.tget l (B.m_heap m3) = Some (B.OExn msg' tv') /\
    exn_ok x msg' /\ mext mu mu' /\ SMs_v1 mu' s' m3).

(* preservation'_statement's conclusion, as a predicate. *)
Definition PresC (n : nat) (mu : kmap) (c : config) (m : B.machine) (rs : nat -> B.jreq -> B.jres) : Prop :=
 (exists c' m' k tS tT mu', Srun c tS c' /\ TRun rs k m tT m' /\ (n <= k)%nat /\ map Some tS = tT /\
    mext mu mu' /\ MS' mu' c' m') \/
 (exists m1 k tS tT, Ends' mu c m1 tS /\ TRun rs k m tT m1 /\ map Some tS = tT).

Ltac split6 := refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).

Lemma mext_refl : forall mu, pbij mu -> mext mu mu.
Proof. intros mu P. split; [intros a A; exact A|exact P]. Qed.

Lemma mext_trans : forall a b c, mext a b -> mext b c -> mext a c.
Proof. intros a b c [I1 _] [I2 P2]. split; [intros x X; apply I2, I1, X|exact P2]. Qed.

Lemma ms'_pbij : forall mu c m, MS' mu c m -> pbij mu.
Proof.
 intros mu c m H. destruct H as [cv caps g top e dst r2 rho k s w m _ X|cv caps g top e l r2 rho k s w m _ X
   |cv caps g top e o top2 r2 rho k s w m _ X|cv caps v v' o k s w m X _ _ _ _ _].
 - exact (sm_bij _ _ _ (proj1 (proj1 X))).
 - exact (sm_bij _ _ _ (proj1 (proj1 X))).
 - exact (sm_bij _ _ _ (proj1 (proj1 X))).
 - exact (sm_bij _ _ _ (proj1 X)).
Qed.

Lemma trun_app_silent : forall rs j m m1, TRun rs j m [] m1 -> forall k t m2, TRun rs k m1 t m2 -> TRun rs (j + k) m t m2.
Proof.
 intros rs j m m1 H. remember (@nil (option event)) as t0 eqn:Et.
 induction H as [rs m|rs n m ma t0 m2 N H IH|rs n m q kk t0 m2 N H IH]; intros k t m3 K; [exact K| |discriminate].
 cbn. eapply TR_tau; [exact N|]. apply IH; auto.
Qed.

Lemma tstar_trun : forall m m1, TStar m m1 -> forall rs, exists j, TRun rs j m [] m1.
Proof.
 intros m m1 H. induction H as [m|m ma m2 T H IH]; intros rs; [exists 0%nat; constructor|].
 destruct (IH rs) as [j J]. exists (S j). eapply TR_tau; [exact T|exact J].
Qed.

Lemma tplus_trun : forall m m1, TPlus m m1 -> forall rs, exists j, (1 <= j)%nat /\ TRun rs j m [] m1.
Proof.
 intros m m1 [ma [T H]] rs. destruct (tstar_trun ma m1 H rs) as [j J]. exists (S j). split; [lia|].
 eapply TR_tau; [exact T|exact J].
Qed.

Lemma srun_app : forall a t b u c, Srun a t b -> Srun b u c -> Srun a (t ++ u) c.
Proof. intros a t b u c H K. unfold JitEmitInv.Srun in *. eapply star_trans; eauto. Qed.

Lemma sstar_srun' : forall a b t c, Sstar a b -> Srun b t c -> Srun a t c.
Proof. intros a b t c H K. change t with ([] ++ t). eapply srun_app; [apply sstar_srun; exact H|exact K]. Qed.

Lemma ends'_pre : forall mu mu' a c m1 t tS, Srun a t c -> mext mu mu' -> Ends' mu' c m1 tS -> Ends' mu a m1 (t ++ tS).
Proof.
 intros mu mu' a c m1 t tS Sr Mx H. destruct H as [v v' s' m2 mu'' S1 Nf M2 Vr Ss|x l msg tv s' m2 mu'' S1 Nf Lh Xo M2 Ss].
 - eapply E'_ok; [eapply srun_app; eauto|exact Nf|eapply mext_trans; eauto|exact Vr|exact Ss].
 - eapply E'_err; [eapply srun_app; eauto|exact Nf|exact Lh|exact Xo|eapply mext_trans; eauto|exact Ss].
Qed.

(* A silent source prefix and a nonempty silent machine prefix, before PresC n: PresC (S n). *)
Lemma presc_step : forall n mu mu' c c' m m' rs, Sstar c c' -> TPlus m m' -> mext mu mu' -> PresC n mu' c' m' rs ->
 PresC (S n) mu c m rs.
Proof.
 intros n mu mu' c c' m m' rs Ss Tp Mx P. destruct (tplus_trun m m' Tp rs) as (j & Lj & J).
 destruct P as [(c2 & m2 & k & tS & tT & mu2 & S2 & T2 & Le & Mp & M2 & Ms)|(m1 & k & tS & tT & En & T2 & Mp)].
 - left. exists c2, m2, (j + k)%nat, tS, tT, mu2. split6.
   + eapply sstar_srun'; eauto.
   + eapply trun_app_silent; eauto.
   + lia.
   + exact Mp.
   + eapply mext_trans; eauto.
   + exact Ms.
 - right. exists m1, (j + k)%nat, tS, tT. split; [|split; [eapply trun_app_silent; eauto|exact Mp]].
   change tS with ([] ++ tS). eapply ends'_pre; [apply sstar_srun; exact Ss|exact Mx|exact En].
Qed.

(* A silent source prefix, before PresC n at the same machine. *)
Lemma presc_src : forall n mu mu' c c' m rs, Sstar c c' -> mext mu mu' -> PresC n mu' c' m rs -> PresC n mu c m rs.
Proof.
 intros n mu mu' c c' m rs Ss Mx P.
 destruct P as [(c2 & m2 & k & tS & tT & mu2 & S2 & T2 & Le & Mp & M2 & Ms)|(m1 & k & tS & tT & En & T2 & Mp)].
 - left. exists c2, m2, k, tS, tT, mu2. split6; auto; [eapply sstar_srun'; eauto|eapply mext_trans; eauto].
 - right. exists m1, k, tS, tT. split; [|split; auto].
   change tS with ([] ++ tS). eapply ends'_pre; [apply sstar_srun; exact Ss|exact Mx|exact En].
Qed.

Lemma env_ok_shift : forall rs, env_ok rs -> env_ok (fun i => rs (S i)).
Proof. intros rs H i q. exact (H (S i) q). Qed.

(* preservation' from sim' and the raise resolution. *)
Theorem preservation'_of_sim' : sim'_statement E pt sealed -> raise_resolve_statement -> preservation'_statement E pt sealed.
Proof.
 intros Sim Rr n. induction n as [|n IHn]; intros mu c m rs Eo H.
 - left. exists c, m, 0%nat, [], [], mu. split6; [constructor|constructor|lia|reflexivity|exact (mext_refl _ (ms'_pbij _ _ _ H))|exact H].
 - revert mu m rs Eo H. induction c as [c IHc] using (well_founded_induction (Wf_nat.well_founded_ltof _ msr)).
   intros mu m rs Eo H. fold (PresC (S n) mu c m rs).
   destruct (Sim mu c m H) as [c' m' mu' Ss [Tp|(-> & Lt)] Mx Ms|m1 q kk Ts Nx Hr
     |v v' s' m1 m2 mu' Ss Ts Nf Mx Vr Sms|x l msg tv s' m1 m2 mu' Ss Ts Nf Lh Xo Mx Sms
     |x k s' m1 m2 msg tv mu' cv caps w Ss Ts Nr Xo Mx Sm Cc Fr].
   + eapply presc_step; [exact Ss|exact Tp|exact Mx|]. exact (IHn mu' c' m' rs Eo Ms).
   + eapply presc_src; [exact Ss|exact Mx|]. exact (IHc c' Lt mu' m rs Eo Ms).
   + destruct (Hr (rs O q) (Eo O q)) as (c' & e & mu' & Ev & Sr & Mx & Ms).
     destruct (tstar_trun m m1 Ts rs) as [j J].
     destruct (IHn mu' c' (kk (rs O q)) (fun i => rs (S i)) (env_ok_shift rs Eo) Ms)
       as [(c2 & m2 & k & tS & tT & mu2 & S2 & T2 & Le & Mp & M2 & Ms2)|(mf & k & tS & tT & En & T2 & Mp)].
     * left. exists c2, m2, (j + S k)%nat, (e :: tS), (Some e :: tT), mu2. split6.
       -- change (e :: tS) with ([e] ++ tS). eapply srun_app; eauto.
       -- eapply trun_app_silent; [exact J|]. rewrite <- Ev. eapply TR_io; [exact Nx|exact T2].
       -- lia.
       -- cbn. rewrite Mp. reflexivity.
       -- eapply mext_trans; eauto.
       -- exact Ms2.
     * right. exists mf, (j + S k)%nat, (e :: tS), (Some e :: tT). split; [|split].
       -- change (e :: tS) with ([e] ++ tS). eapply ends'_pre; eauto.
       -- eapply trun_app_silent; [exact J|]. rewrite <- Ev. eapply TR_io; [exact Nx|exact T2].
       -- cbn. rewrite Mp. reflexivity.
   + right. destruct (tstar_trun m m1 Ts rs) as [j J]. exists m1, j, [], [].
     split; [|split; [exact J|reflexivity]]. eapply E'_ok; [apply sstar_srun; exact Ss|exact Nf|exact Mx|exact Vr|exact Sms].
   + right. destruct (tstar_trun m m1 Ts rs) as [j J]. exists m1, j, [], [].
     split; [|split; [exact J|reflexivity]].
     eapply E'_err; [apply sstar_srun; exact Ss|exact Nf|exact Lh|exact Xo|exact Mx|exact Sms].
   + destruct (Rr mu' x k s' m1 m2 msg tv cv caps w Nr Xo Sm Cc Fr)
       as [(c2 & m3 & mu2 & S2 & Tp & M2 & Ms2)|(l & msg' & tv' & s2 & m3 & mu2 & S2 & Nf & Lh & Xo' & M2 & Sms)].
     * eapply presc_step; [eapply Sstar_trans; [exact Ss|exact S2]| |eapply mext_trans; [exact Mx|exact M2]|].
       -- assert (Tp1 : TPlus m1 m3) by (first [exact Tp|eauto]).
          destruct Tp1 as (ma & T1 & T2). destruct Ts as [|m0 mb m1' T0 T3].
          ++ exists ma. split; [exact T1|exact T2].
          ++ exists mb. split; [exact T0|]. eapply TStar_trans; [exact T3|]. econstructor; [exact T1|exact T2].
       -- exact (IHn mu2 c2 m3 rs Eo Ms2).
     * right. destruct (tstar_trun m m1 Ts rs) as [j J]. exists m1, j, [], [].
       split; [|split; [exact J|reflexivity]].
       eapply E'_err; [apply sstar_srun; eapply Sstar_trans; [exact Ss|exact S2]|exact Nf|exact Lh|exact Xo'
         |eapply mext_trans; [exact Mx|exact M2]|exact Sms].
Qed.

(* The call statement, from sim' and the raise resolution. *)
Theorem call_preservation'_of_sim' : sim'_statement E pt sealed -> raise_resolve_statement -> call_preservation'_statement E pt sealed.
Proof. intros Sim Rr. exact (call_preservation'_of_preservation' (preservation'_of_sim' Sim Rr)). Qed.
End Gen.

(* ---------- the slot-1 gap (closed witnesses) ----------
   EvalCtx (and TestCtx, OpCtx) ask (cv = [] \/ ~ w (fp + 1)) of the w their continuation is at:
   a code that captures never writes its closure's slot. JitEmitKont's frames whose body runs at
   an inner w1 (KD'_let, KD'_lett, KD'_trap, KD'_do1, KD'_do1t, KD'_hbind, TK'_if, TK'_cond,
   TK'_and, TK'_or) relate w1 to the outer w by Sub w w1 and Above fp top w1 only, so nothing keeps
   fp + 1 out of w1; a body whose destination is slot 1 (KC'_slot) even needs it in. Then MS'
   relates the source at Ret to a machine whose next source state (the frame's body) no EvalCtx at
   that code and cv relates (ms'_slot1_frame, evalctx_slot1_void). A generic proof of sim'_statement
   from the sim_X_statement must re-relate that state; at another cv it would need Comp at that cv,
   which the family hooks need not give. So the Ret cases of sim'_of_sims are not provable
   generically on these frames. What a frame would need is (cv = [] \/ ~ w1 (fp + 1)), or a
   destination other than slot 1 with 2 <= top (a change to JitEmitKont, emit-spec's to make).
   Does NOT say: that sim'_statement is false. With the hooks empty no code reads a capture, and a
   concrete state can be re-related at cv = []; whether some family rule makes it false is UNKNOWN. *)
Lemma lookup_cons_eq0 : forall {A} x (a : A) (rho : list (name * A)), lookup x ((x, a) :: rho) = Some a.
Proof. intros A x a rho. cbn. rewrite text_eqb_refl. reflexivity. Qed.

Lemma evalctx_slot1_void : forall mu cv caps g top r2 rho k s w m, cv <> [] ->
 ~ EvalCtx mu cv caps g top (DSlot 1) r2 rho k s w m.
Proof.
 intros mu cv caps g top r2 rho k s w m Ncv (_ & _ & _ & _ & _ & Wf & Kc).
 destruct Wf as [Ecv|Nw]; [subst cv; congruence|]. inversion Kc; subst. contradiction.
Qed.

Definition sl_z : name := JitEmitInv.cx_z.
Definition sl_x : name := JitEmitInv.cx_x.
Definition sl_r2 : list B.instr := [B.IReturn (B.OSlot 1)].
Definition sl_r : list B.instr := B.IMove 1 3 :: sl_r2.
Definition sl_st : B.tree B.val :=
 B.tset (B.skey 1) (B.VClo 1) (B.tset (B.skey 2) (B.VFix 5) (B.tset (B.skey 3) (B.VFix 0) B.Leaf)).
Definition sl_m : B.machine :=
 B.Machine sl_st 0 JitEmitInv.cx_do sl_r [] [] B.VCleared JitEmitInv.cx_heap 2 B.Leaf JitEmitInv.cx_gfun B.Leaf false 0.
Definition sl_rho : lenv := [(sl_z, VNum (NInt 0))].
Definition sl_k : list frame := [KLet sl_x (EVar sl_z) sl_rho].
Definition sl_c : config := Cfg (Ret (VNum (NInt 5))) sl_k JitEmitInv.cx_s.

(* MS' relates the source at Ret with a let frame whose body (Z, in slot 3) goes to slot 1, in a
   code that captures Z (cv = [Z], its closure in slot 1), to the machine at that body. *)
Lemma ms'_slot1_frame : MS' [] sl_c sl_m.
Proof.
 unfold sl_c, sl_k.
 eapply MS'_ret with (cv := [sl_z]) (caps := []) (o := B.OSlot 2) (v' := B.VFix 5) (w := fun a => (4 <= a)%N).
 - split.
   + constructor.
     * exact pbij_nil.
     * intros l p I; destruct I.
     * split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate].
     * apply funrel_embed. apply JitEmitInv.cx_funrel; reflexivity.
     * apply JitEmitInv.cx_fresh; [reflexivity|cbn; lia].
   + unfold HK. cbn. constructor.
 - vm_compute. reflexivity.
 - constructor.
 - right. exists 1%positive. split; [vm_compute; reflexivity|vm_compute; reflexivity].
 - right. cbn. lia.
 - eapply KD'_let with (g := [(sl_z, 3)]) (top := 4) (dst := DSlot 1) (r2 := sl_r2) (w1 := fun a => (1 <= a)%N).
   + split.
     * intros x s0 L. assert (L' : (if text_eqb x sl_z then Some 3%N else None) = Some s0) by exact L.
       destruct (text_eqb x sl_z) eqn:T; [|discriminate]. inversion L'; subst.
       apply text_eqb_eq in T; subst x. exists (VNum (NInt 0)), (B.VFix 0).
       split; [unfold sl_rho; apply lookup_cons_eq0|split; [vm_compute; reflexivity|constructor]].
     * intros i x Ni Lx. destruct i as [|[|i]]; cbn in Ni; try discriminate. inversion Ni; subst.
       assert (Lx' : (if text_eqb sl_z sl_z then Some 3%N else None) = None) by exact Lx.
       rewrite text_eqb_refl in Lx'. discriminate.
   + intros x s0 L. assert (L' : (if text_eqb x sl_z then Some 3%N else None) = Some s0) by exact L.
     destruct (text_eqb x sl_z); [inversion L'; subst; cbn; lia|discriminate].
   + intros x s0 L. assert (L' : (if text_eqb x sl_z then Some 3%N else None) = Some s0) by exact L.
     destruct (text_eqb x sl_z); [inversion L'; subst; lia|discriminate].
   + lia.
   + eapply C_move; [vm_compute; reflexivity|lia].
   + intros a A; cbn in A |- *; lia.
   + intros a A; lia.
   + apply KC'_slot; [cbn; lia|]. apply KD'_ret; [intros a A; cbn in *; lia|constructor].
Qed.

(* ---------- the statements are FALSE as stated: a stale allocation pointer (closed) ----------
   SM (SMs: sm_bij, sm_heap, sm_gvals, sm_fun) says nothing about the machine's next allocation key
   m_next, and JitBytecode.alloc writes at m_next without looking. So SM relates a machine whose
   m_next is the key of a live object, here do's closure (key 1 of JitEmitInv.cx_heap, which
   FunRel' ties to the store's do). The call fx_c of (defun f (X) (hd X)) on 1 is accepted
   (CompFn' through C_ret, O_val, C_prim, O_var; no family hook) and entered with 1 in slot 2. The
   machine's first step raises "hd: 1 is not a pair" with no handler, allocating the exception at
   key 1 over do's closure, and finishes (fx_next). Every end Ends' or EndsSrc' admits asks SMs of
   that final machine, whose FunRel' fails for EVERY store (fx_no_funrel: the global function do
   is a closure at key 1, which no longer holds one). And the machine has no step to stay related
   after. So, at n = 1, neither disjunct holds:
   - call_preservation'_false: ~ call_preservation'_statement cx_E cx_pt [];
   - preservation'_false: ~ preservation'_statement cx_E cx_pt [] (through
     call_preservation'_of_preservation');
   - call_preservation_src'_false: ~ call_preservation_src'_statement cx_E cx_pt [] [] (b0 = b1 = e,
     the KRef links by KRef_refl, D = []).
   What the statements need: SMs to keep m_next fresh (every key at or above it unused). That is
   r21-sms-fresh-fix's JitEmitInv.Fresh and sm_fresh; the refutations below are of the v1 text
   (SM_v1, SMs_v1, MS'_v1, Ends'_v1, EndsSrc'_v1), kept as it was refuted.
   Does NOT say: anything about a machine whose m_next is fresh (every machine the loader builds
   and every run from one), or about sim'_statement, which O'_raise satisfies before the allocation
   (its SM is of the machine that raises); the refutation is of the many-step statements' ends. *)
Definition fx_x : name := JitEmitInv.cx_x.
Definition fx_b : expr := ECall (of_string "hd") [EVar fx_x].
Definition fx_r : list B.instr := [B.IPrim 3 B.PHd [B.OSlot 2]; B.IReturn (B.OSlot 3)].
Definition fx_c : B.code := B.Code B.VNil 1 None 5 [] fx_r [] B.VNil.
Definition fx_st : B.tree B.val := B.tset (B.skey 2) (B.VFix 1) B.Leaf.
Definition fx_m : B.machine :=
 B.Machine fx_st 0 fx_c fx_r [] [] B.VCleared JitEmitInv.cx_heap 1 B.Leaf JitEmitInv.cx_gfun B.Leaf false 0.
Definition fx_args : list value := [VNum (NInt 1)].

Lemma fx_sm : SM_v1 [] JitEmitInv.cx_s [] fx_m.
Proof.
 split.
 - constructor.
   + exact pbij_nil.
   + intros l p I; destruct I.
   + split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate].
   + apply funrel_embed. apply JitEmitInv.cx_funrel; reflexivity.
 - unfold HK. cbn. constructor.
Qed.

Lemma fx_comp : CompFn' fx_c [fx_x] fx_b.
Proof.
 exists []. eapply C_ret. eapply O_val. eapply C_prim with (p := PHd) (q := B.PHd) (ops := [B.OSlot 2]).
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - discriminate.
 - eapply Os_cons; [eapply O_var; [vm_compute; reflexivity|lia]|apply Os_nil].
 - reflexivity.
Qed.

Lemma fx_entered : entered' [] fx_m fx_c fx_args.
Proof.
 split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
 eapply AA'_cons; [vm_compute; reflexivity|constructor|constructor].
Qed.

Lemma fx_next : exists m', B.next JitEmitInv.cx_E JitEmitInv.cx_pt fx_m = B.MFinal (B.FError (B.VExn 1)) m' /\
 B.m_gfun m' = JitEmitInv.cx_gfun /\ exists msg tv, B.tget 1 (B.m_heap m') = Some (B.OExn msg tv).
Proof.
 eexists. split; [vm_compute; reflexivity|]. split; [reflexivity|]. eexists _, _. vm_compute. reflexivity.
Qed.

Lemma fx_no_funrel : forall s m', B.m_gfun m' = JitEmitInv.cx_gfun ->
 (forall c caps, B.tget 1 (B.m_heap m') <> Some (B.OClo c caps)) -> ~ FunRel' s m'.
Proof.
 intros s m' G H Fr. assert (Gd : B.tget (B.sym_of_text do_name) (B.m_gfun m') = Some (B.VClo 1)).
 { rewrite G. apply JitMeta.JitMeta.tget_tset_same. }
 destruct (lookup do_name (gfuns s)) as [[p|ps b]|] eqn:L.
 - pose proof (fr'_prim _ _ Fr _ _ L) as Pn. rewrite JitEmitInv.do_not_prim in Pn. discriminate.
 - destruct (fr'_user _ _ Fr _ _ _ L) as (l & c & caps & Gl & Hl & _). rewrite Gd in Gl. inversion Gl; subst.
   exact (H c caps Hl).
 - exact (fr'_none _ _ Fr _ L 1 Gd).
Qed.

(* The final machine of any end from fx_m: none is SMs-related to any store. *)
Lemma fx_final_bad : forall o m2, B.next JitEmitInv.cx_E JitEmitInv.cx_pt fx_m = B.MFinal o m2 ->
 (forall v', o <> B.FReturn v') /\ forall mu s, ~ SMs_v1 mu s m2.
Proof.
 intros o m2 N. destruct fx_next as (m' & Nx & G & msg & tv & Hl). rewrite Nx in N. injection N as <- <-.
 split; [intros v' E0; discriminate|]. intros mu s Ss. apply (fx_no_funrel s m' G); [|exact (sm_fun_v1 _ _ _ Ss)].
 intros c caps E0. rewrite Hl in E0. discriminate.
Qed.

Lemma fx_trun : forall rs k tT m1, TRun JitEmitInv.cx_E JitEmitInv.cx_pt rs k fx_m tT m1 -> k = 0%nat /\ m1 = fx_m.
Proof.
 intros rs k tT m1 Tr. destruct fx_next as (m' & Nx & _). inversion Tr; subst; [split; reflexivity| |];
  match goal with N : B.next _ _ fx_m = _ |- _ => rewrite Nx in N; discriminate end.
Qed.

Theorem call_preservation'_false : ~ call_preservation'_statement_v1 JitEmitInv.cx_E JitEmitInv.cx_pt [].
Proof.
 intro Cp. destruct env_ok_inhabited as [rs Eo].
 destruct (Cp [] JitEmitInv.cx_s fx_m fx_c [fx_x] fx_b fx_args 1%nat rs Eo fx_sm fx_comp eq_refl fx_entered)
   as [(c' & m' & k & tS & tT & mu' & _ & Tr & Le & _)|(m1 & k & tS & tT & En & Tr & _)].
 - destruct (fx_trun rs k tT m' Tr) as [-> _]. lia.
 - destruct (fx_trun rs k tT m1 Tr) as [_ ->].
   destruct En as [v v' s' m2 mu' _ Nf _ _ Ss|x l msg tv s' m2 mu' _ Nf _ _ _ Ss];
     destruct (fx_final_bad _ _ Nf) as [Nr Ns]; [exact (Nr v' eq_refl)|exact (Ns _ _ Ss)].
Qed.

Theorem preservation'_false : ~ preservation'_statement_v1 JitEmitInv.cx_E JitEmitInv.cx_pt [].
Proof. intro P. exact (call_preservation'_false (call_preservation'_of_preservation'_v1 _ _ _ P)). Qed.

Theorem call_preservation_src'_false : ~ call_preservation_src'_statement_v1 JitEmitInv.cx_E JitEmitInv.cx_pt [] [].
Proof.
 intro Cp. destruct env_ok_inhabited as [rs Eo].
 assert (Dw : JitKRef.JitKRef.D_wf [] []) by (split; constructor).
 assert (Kr : JitKRef.JitKRef.KRef [] [] [fx_x] fx_b fx_b)
   by (apply (JitKRefFund.JitKRefFund.KRef_refl [] [] [fx_x] fx_b Dw); vm_compute; reflexivity).
 assert (Sh : JitKRef.JitKRef.StoreHas [] JitEmitInv.cx_s) by (intros f d I; destruct I).
 assert (So : store_ok JitEmitInv.cx_s) by (split; constructor).
 destruct (Cp [] JitEmitInv.cx_s fx_m fx_c [fx_x] fx_b fx_b fx_b fx_args 1%nat rs Eo Dw Kr Kr Sh So fx_sm fx_comp eq_refl fx_entered)
   as [(c' & m' & k & tS & tT & mu' & _ & Tr & Le & _)|(m1 & k & tS & tT & En & Tr & _)].
 - destruct (fx_trun rs k tT m' Tr) as [-> _]. lia.
 - destruct (fx_trun rs k tT m1 Tr) as [_ ->].
   destruct En as [v0 v v' s0 s' w m2 mu' _ _ _ _ Nf _ _ Ss|x l msg tv s0 s' w m2 mu' _ _ _ Nf _ _ _ Ss];
     destruct (fx_final_bad _ _ Nf) as [Nr Ns]; [exact (Nr v' eq_refl)|exact (Ns _ _ Ss)].
Qed.

(* raise_resolve_statement (preservation'_of_sim''s premise) is FALSE as stated, by the same stale
   pointer: at fx_m the machine raises from fx_m with its rest advanced (fx_raise), SM and an empty
   continuation relate that machine, and the only resolution, the no-handler end, asks SMs of the
   machine after the allocation (fx_final_bad). So preservation'_of_sim' is an implication from a
   false premise at cx_E; it says what the many-step proof needs once SMs keeps m_next fresh. *)
Definition fx_m2 : B.machine := B.set_rest fx_m [B.IReturn (B.OSlot 3)].
Lemma fx_raise : B.next JitEmitInv.cx_E JitEmitInv.cx_pt fx_m = B.raise fx_m2 (B.t "hd: ~S is not a pair") (B.VFix 1).
Proof. vm_compute. reflexivity. Qed.

Theorem raise_resolve_false : ~ raise_resolve_statement_v1 JitEmitInv.cx_E JitEmitInv.cx_pt [].
Proof.
 intro Rr.
 assert (Sm : SM_v1 [] JitEmitInv.cx_s [] fx_m2).
 { split.
   - constructor.
     + exact pbij_nil.
     + intros l p I; destruct I.
     + split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate].
     + apply funrel_embed. apply JitEmitInv.cx_funrel; reflexivity.
   - unfold HK. cbn. constructor. }
 destruct (Rr [] XNotCallable [] JitEmitInv.cx_s fx_m fx_m2 (B.t "hd: ~S is not a pair") (B.VFix 1) [] [] (fun a => (0 <= a)%N)
   fx_raise I Sm (or_introl eq_refl))
   as [(c' & m' & mu' & _ & (ma & T1 & _) & _)|(l & msg' & tv' & s' & m3 & mu' & _ & Nf & _ & _ & _ & Ss)].
 - right. right. exists DRet, []. apply KC'_ret; [intros a A; exact A|constructor].
 - destruct fx_next as (mx & Nx & _). unfold TS in T1. rewrite Nx in T1. discriminate.
 - exact (proj2 (fx_final_bad _ _ Nf) _ _ Ss).
Qed.

(* ---------- after the repair (r21-sms-fresh-fix, closed) ----------
   SMs now asks sm_fresh (JitEmitInv.Fresh: no heap key at or above m_next in use). fx_m's m_next
   is the key of do's closure, so no SM relates it, at any mu, store or continuation (fx_not_sm):
   the counterexamples above say nothing about the corrected statements. But fx_m meets every
   premise of the old statements (JitKRef.call_preservation_src_statement at 4a7346e and
   JitLowerThm.call_preservation: Com, CompFn, entered), and GvalsRel [] too (fresh_needed). So no
   corollary takes the corrected call_preservation_src'_statement to the byte-identical old
   statement by instantiating it at the old premises: Fresh m must be added, as GvalsRel [] s m
   already was (JitEmitInv.gvals_needed); the target reached is
   JitEmitInv.call_preservation_src_old_fresh_statement (call_preservation_src_old_of_cp').
   Does NOT say: that the corrected statements are true (sim'_statement, raise_resolve_statement
   and clo_scoped_statement are not proved), or that the old statement is false (it is proved,
   JitKRefFund.call_preservation_src). *)
Lemma fx_not_sm : forall mu s k, ~ SM mu s k fx_m.
Proof.
 intros mu s k [Ss _]. pose proof (sm_fresh _ _ _ Ss 1%positive (Pos.le_refl _)) as F.
 cbn in F. discriminate F.
Qed.

Lemma fx_comp_old : JitLowerRel.CompFn fx_c [fx_x] fx_b.
Proof.
 exists []. eapply JitLowerRel.C_ret. eapply JitLowerRel.O_val.
 eapply JitLowerRel.C_prim with (p := PHd) (q := B.PHd) (ops := [B.OSlot 2]).
 - vm_compute. reflexivity.
 - reflexivity.
 - reflexivity.
 - discriminate.
 - eapply JitLowerRel.Os_cons; [eapply JitLowerRel.O_var; [vm_compute; reflexivity|lia]|apply JitLowerRel.Os_nil].
 - reflexivity.
Qed.

Example fresh_needed : Com JitEmitInv.cx_s fx_m /\ JitLowerRel.CompFn fx_c [fx_x] fx_b /\
 List.length [fx_x] = List.length fx_args /\ JitLowerThm.entered fx_m fx_c fx_args /\
 GvalsRel [] JitEmitInv.cx_s fx_m /\ ~ Fresh fx_m /\ forall mu s k, ~ SM mu s k fx_m.
Proof.
 split; [split; [reflexivity|apply JitEmitInv.cx_funrel; reflexivity]|].
 split; [exact fx_comp_old|]. split; [reflexivity|].
 split; [split; [reflexivity|split; [reflexivity|split; [reflexivity|]]];
   eapply JitLowerKont.AA_cons; [vm_compute; reflexivity|constructor|constructor]|].
 split; [split; [intros x v L; discriminate|intros x _ v' T; cbn in T; rewrite JitMeta.JitMeta.tget_leaf in T; discriminate]|].
 split; [intro F; pose proof (F 1%positive (Pos.le_refl _)) as F1; cbn in F1; discriminate F1|].
 exact fx_not_sm.
Qed.

(* ---------- the front end composed ---------- *)
(* The one fact about closure bodies the composition needs beyond JitEmitInv's statements: a body
   CloOK accepts reads no variable outside its parameters and its capture names. Then a closure
   VRh relates is VRel-related to itself through KRef_refl, whatever else its environment holds
   (VRh_lam constrains only the captured entries, so the environment need not be vok, and
   JitKRefGround.vrefl does not apply).
   NOT proved here: with the hooks opaque, Comp gives scoping only through each family's own rule
   (the Clo hook's capture reads), so it is a per-family lemma through Comp_ind' (emit-assembly).
   Does NOT say: anything about a closure that is not CloOK (VRh relates none), or about the
   bytecode. *)
Definition clo_scoped_statement : Prop :=
 forall nc cv ps b, CloOK nc cv ps b -> JitKRef.JitKRef.scoped (ps ++ cv) b = true.

Section Src.
Variables (E : B.env) (pt : B.tree (B.prim * nat)) (sealed : list name) (D : list (name * fundef)).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation VRelF := (JitKRef.JitKRef.VRelF sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation StoreHas := (JitKRef.JitKRef.StoreHas D).
Notation world := JitKRef.JitKRef.world.
Notation wf_world := JitKRef.JitKRef.wf_world.
Notation wext := JitKRef.JitKRef.wext.
Notation id_world := JitKRef.JitKRef.id_world.
Notation GVal := JitKRef.JitKRef.GVal.
Notation GStore := JitKRef.JitKRef.GStore.
Notation VRel_unfold := (JitKRefGround.JitKRefGround.VRel_unfold sealed D).
Notation VRelF_index := (JitKRefGround.JitKRefGround.VRelF_index sealed D).
Notation ERel_with_ext := (JitKRefGround.JitKRefGround.ERel_with_ext sealed D).
Notation id_world_in := JitKRefGround.JitKRefGround.id_world_in.
Notation id_world_wf := JitKRefGround.JitKRefGround.id_world_wf.

Lemma nth_error_In_ex : forall (l : list name) y, In y l -> exists i, nth_error l i = Some y.
Proof. intros l y I. apply In_nth_error in I. exact I. Qed.

Lemma lookup_cons_ne : forall {A} x y (a : A) (rho : list (name * A)), x <> y -> lookup y ((x, a) :: rho) = lookup y rho.
Proof.
 intros A x y a rho N. cbn. destruct (text_eqb y x) eqn:T; [apply text_eqb_eq in T; congruence|reflexivity].
Qed.

Lemma lookup_cons_eq : forall {A} x (a : A) (rho : list (name * A)), lookup x ((x, a) :: rho) = Some a.
Proof. intros A x a rho. cbn. rewrite text_eqb_refl. reflexivity. Qed.

(* A value VRh relates, under a mu each of whose source cells the store has, is VRel-reflexive at
   every index and world extending the identity on the store. *)
Lemma vrh_refl : D_wf -> clo_scoped_statement -> forall mu s h, (forall l p, In (l, p) mu -> (l < List.length (heap s))%nat) ->
 forall v v', VRh mu h v v' -> forall k w, wf_world w -> incl (id_world s) w -> VRel k w v v.
Proof.
 intros Dw Hs mu s h Hmu. fix IH 3.
 intros v v' H k w Ww Iw.
 destruct H as [z|b|x|b|t| |a a' d d' Ha Hd|l p cells Il Tp|x b rho p nc caps cv l0 Tp Ck Ci Il Lc Hc
   |b rho p nc caps cv l0 Tp Ck Ci Il Lc Hc|x p msg tv Tp Xo|hd p d o Tp];
   rewrite VRel_unfold; cbn [JitKRef.JitKRef.VBody]; try reflexivity; try exact I.
 - split; rewrite <- VRel_unfold; [exact (IH _ _ Ha k w Ww Iw)|exact (IH _ _ Hd k w Ww Iw)].
 - apply Iw, id_world_in. exact (Hmu l p Il).
 - split.
   + unfold JitKRef.JitKRef.same_id. rewrite Ci. apply Iw, id_world_in. exact (Hmu l0 p Il).
   + destruct k as [|k]; [intros j L; lia|].
     intros j L w' [Iw' W'] a0 a A. cbv beta iota in A |- *.
     rewrite (VRelF_index k j ltac:(lia)) in A.
     eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
     apply (JitKRefFund.JitKRefFund.KRef_refl sealed D (x :: cv) b Dw (Hs nc cv [x] b Ck) j w' _ _ W').
     intros y [<-|Iy].
     * exists a0, a. rewrite !lookup_cons_eq. split; [reflexivity|split; [reflexivity|exact A]].
     * destruct (text_eqb y x) eqn:Tyx.
       { apply text_eqb_eq in Tyx. subst y. exists a0, a. rewrite !lookup_cons_eq. split; [reflexivity|split; [reflexivity|exact A]]. }
       assert (Nyx : x <> y) by (intro E0; subst y; rewrite text_eqb_refl in Tyx; discriminate).
       destruct (nth_error_In_ex cv y Iy) as [i Ni].
       assert (Lb : lookup y (bind [x] 2) = None) by (cbn; rewrite Tyx; reflexivity).
       destruct (Hc i y Ni Lb) as (u & u' & Lu & _ & Vu).
       exists u, u. rewrite !lookup_cons_ne by exact Nyx. split; [exact Lu|split; [exact Lu|]].
       exact (IH _ _ Vu j w' W' (fun q Q => Iw' q (Iw q Q))).
 - split.
   + unfold JitKRef.JitKRef.same_id. rewrite Ci. apply Iw, id_world_in. exact (Hmu l0 p Il).
   + destruct k as [|k]; [intros j L; lia|].
     intros j L w' [Iw' W']. cbv beta iota.
     eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
     apply (JitKRefFund.JitKRefFund.KRef_refl sealed D cv b Dw (Hs nc cv [] b Ck) j w' _ _ W').
     intros y Iy. destruct (nth_error_In_ex cv y Iy) as [i Ni].
     destruct (Hc i y Ni) as (u & u' & Lu & _ & Vu).
     exists u, u. split; [exact Lu|split; [exact Lu|]].
     exact (IH _ _ Vu j w' W' (fun q Q => Iw' q (Iw q Q))).
Qed.

(* JitKRef's adequacy for any IO trace, from environments whose values are VRel-reflexive at the
   identity world (JitKRefGround.adequacy_of_fundamental: first-order values, silent runs). *)
Lemma adequacy_tr : D_wf -> forall g e0 e rho s, KRef g e0 e ->
 (forall x, In x g -> exists v, lookup x rho = Some v /\ forall k, VRel k (id_world s) v v) ->
 StoreHas s -> store_ok s ->
 (forall t v s', srun (Cfg (Eval rho e) [] s) t (Cfg (Ret v) [] s') -> exists v0 s0 w,
    srun (Cfg (Eval rho e0) [] s) t (Cfg (Ret v0) [] s0) /\ wext (id_world s) w /\ GVal w v0 v /\ GStore w s0 s') /\
 (forall t x s', srun (Cfg (Eval rho e) [] s) t (Cfg (Throw x) [] s') -> exists s0 w,
    srun (Cfg (Eval rho e0) [] s) t (Cfg (Throw x) [] s0) /\ wext (id_world s) w /\ GStore w s0 s').
Proof.
 intros DW g e0 e rho s HK Hdom HS Hok.
 assert (Main : forall n, JitKRef.JitKRef.ObsT sealed (S n) (id_world s) (Cfg (Eval rho e0) [] s) (Cfg (Eval rho e) [] s)).
 { intros n. eapply (HK (S n) (id_world s) rho rho (id_world_wf s)).
   - intros x Ix. destruct (Hdom x Ix) as [v [Lv Rv]]. exists v, v. split; [exact Lv|split; [exact Lv|exact (Rv (S n))]].
   - apply le_n.
   - apply JitKRefGround.JitKRefGround.wext_refl, id_world_wf.
   - apply (JitKRefGround.JitKRefGround.KRel_top sealed D), id_world_wf.
   - exact (JitKRefFund.JitKRefFund.store_refl sealed D (S n) s DW HS Hok). }
 split.
 - intros t v s' Hr. destruct (JitKRefGround.JitKRefGround.srun_runs sealed _ _ _ Hr) as [n Hn].
   destruct (Main n n t _ (Nat.lt_succ_diag_r n) Hn) as [A _].
   destruct (A v s' eq_refl) as (v0 & s0 & w' & S0 & Wx & Gv & Gs). exists v0, s0, w'. auto.
 - intros t x s' Hr. destruct (JitKRefGround.JitKRefGround.srun_runs sealed _ _ _ Hr) as [n Hn].
   destruct (Main n n t _ (Nat.lt_succ_diag_r n) Hn) as [_ [B0 _]].
   destruct (B0 x s' eq_refl) as (s0 & w' & S0 & Wx & Gs). exists s0, w'. auto.
Qed.

Lemma lookup_combine_in : forall (ps : list name) (args : list value) x v, lookup x (combine ps args) = Some v -> In v args.
Proof.
 induction ps as [|y ps IH]; intros [|a args] x v L; cbn in L; try discriminate.
 destruct (text_eqb x y); [inversion L; subst; left; reflexivity|right; eapply IH; exact L].
Qed.

Lemma lookup_combine_some : forall (ps : list name) (args : list value) x,
 List.length ps = List.length args -> In x ps -> exists v, lookup x (combine ps args) = Some v.
Proof.
 induction ps as [|y ps IH]; intros [|v args] x L I; cbn in *; try contradiction; try discriminate.
 destruct (text_eqb x y) eqn:T; [eauto|]. destruct I as [Ex|I].
 - subst. rewrite text_eqb_refl in T. discriminate.
 - apply IH; [lia|exact I].
Qed.

Lemma argsat_in : forall (V : value -> B.val -> Prop) st a args, ArgsAt' V st a args -> forall v, In v args -> exists v', V v v'.
Proof. intros V st a args H; induction H; intros u I; [destruct I|destruct I as [<-|I]; eauto]. Qed.

Lemma heaprel_dom : forall mu s m l p, HeapRel mu s m -> In (l, p) mu -> (l < List.length (heap s))%nat.
Proof.
 intros mu s m l p H I. destruct (H l p I) as [(c0 & c1 & N & _)|(N & _)]; apply nth_error_Some; congruence.
Qed.

(* call_preservation_src' from call_preservation' and clo_scoped: the emitted body's run, which
   call_preservation' relates to the machine, is matched by b1's and then by b0's (adequacy_tr
   twice, from the same start, the arguments VRel-reflexive by vrh_refl), composed with
   GVal_trans and GStore_trans at compose_world. *)
Theorem call_preservation_src'_of_cp' : call_preservation'_statement E pt sealed -> clo_scoped_statement ->
 call_preservation_src'_statement E pt sealed D.
Proof.
 intros Cp Hs mu s m c ps b0 b1 e args n rs Eo Dw K01 K1e Sh So Sm Cf L En c0 ce.
 destruct (Cp mu s m c ps e args n rs Eo Sm Cf L En) as [H|(m1 & k & tS & tT & Ee & Tr & Mp)];
   [left; exact H|right]. exists m1, k, tS, tT. split; [|split; assumption].
 assert (Hdom : forall x, In x ps -> exists v, lookup x (combine ps args) = Some v /\ forall j, VRel j (id_world s) v v).
 { intros x Ix. destruct (lookup_combine_some ps args x L Ix) as [v Lv]. exists v. split; [exact Lv|].
   intros j. destruct (argsat_in _ _ _ _ (proj2 (proj2 (proj2 (proj2 En)))) v (lookup_combine_in _ _ _ _ Lv)) as [v' Vv].
   eapply (vrh_refl Dw Hs mu s _ (fun l p I => heaprel_dom mu s m l p (sm_heap _ _ _ (proj1 Sm)) I) v v' Vv j);
     [apply id_world_wf|intros q Q; exact Q]. }
 destruct (adequacy_tr Dw ps b1 e (combine ps args) s K1e Hdom Sh So) as [A1 B1].
 destruct (adequacy_tr Dw ps b0 b1 (combine ps args) s K01 Hdom Sh So) as [A0 B0].
 destruct Ee as [v v' s' m2 mu' Sr Nf Mx Vr Ss|x l msg tv s' m2 mu' Sr Nf Lh Xo Mx Ss].
 - destruct (A1 tS v s' Sr) as (v1 & s1 & w2 & S1 & W2 & G2 & H2).
   destruct (A0 tS v1 s1 S1) as (v0 & s0 & w1 & S0 & W1 & G1 & H1).
   eapply ES'_ok with (v0 := v0) (s0 := s0) (w := JitKRef.JitKRef.compose_world w1 w2); [exact S0| | | |exact Nf|exact Mx|exact Vr|exact Ss].
   + apply JitKRefGround.JitKRefGround.wext_compose_id; assumption.
   + exact (proj1 (JitKRefGround.JitKRefGround.GVal_trans _ _ _ _ _ (proj2 W1) (proj2 W2) G1 G2)).
   + eapply JitKRefGround.JitKRefGround.GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact H1|exact H2].
 - destruct (B1 tS x s' Sr) as (s1 & w2 & S1 & W2 & H2).
   destruct (B0 tS x s1 S1) as (s0 & w1 & S0 & W1 & H1).
   eapply ES'_err with (s0 := s0) (w := JitKRef.JitKRef.compose_world w1 w2); [exact S0| | |exact Nf|exact Lh|exact Xo|exact Mx|exact Ss].
   + apply JitKRefGround.JitKRefGround.wext_compose_id; assumption.
   + eapply JitKRefGround.JitKRefGround.GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact H1|exact H2].
Qed.

(* The old fragment's src statement (JitKRef.call_preservation_src_statement at mu = [], with
   GvalsRel [] s m and Fresh m added; JitEmitInv.call_preservation_src_old_fresh_statement) from
   call_preservation', clo_scoped and the catch-up reflection, through
   JitEmitInv.call_preservation_src_old_of_new''. Its conclusion is the old statement's, verbatim;
   its premises are the old ones plus those two (fresh_needed, JitEmitInv.gvals_needed: neither
   follows from the old premises, and the corrected statements say nothing without them). *)
Theorem call_preservation_src_old_of_cp' : call_preservation'_statement E pt sealed -> clo_scoped_statement ->
 old_reflect'_statement E pt sealed -> call_preservation_src_old_fresh_statement E pt sealed D.
Proof.
 intros Cp Hs Rf. exact (call_preservation_src_old_of_new'' E pt sealed D (call_preservation_src'_of_cp' Cp Hs) Rf).
Qed.
End Src.
End JitEmitSim.
