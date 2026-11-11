(* Shen/JIT Phase 2, emit-sim (task r22-emit-sim): the generic parts of the extended back end's
   correctness statements (JitEmitInv), as implications between statements, every one closed.
   NOTHING here is assumed or Admitted; each theorem takes the statements it uses as explicit
   arguments, so Print Assumptions shows no axiom.

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
End Gen.

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
   GvalsRel [] s m added; JitEmitInv.call_preservation_src_old_statement) from call_preservation',
   clo_scoped and the catch-up reflection, through JitEmitInv.call_preservation_src_old_of_new''. *)
Theorem call_preservation_src_old_of_cp' : call_preservation'_statement E pt sealed -> clo_scoped_statement ->
 old_reflect'_statement E pt sealed -> call_preservation_src_old_statement E pt sealed D.
Proof.
 intros Cp Hs Rf. exact (call_preservation_src_old_of_new'' E pt sealed D (call_preservation_src'_of_cp' Cp Hs) Rf).
Qed.
End Src.
End JitEmitSim.
