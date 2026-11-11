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
End JitEmitSim.
