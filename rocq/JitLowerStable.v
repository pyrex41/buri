(* Shen/JIT Phase 2: preservation from KLambda (KLPort.step_r under jit_rules) to the bytecode
   (JitBytecode.next), over the relation in JitLowerRel.v. It covers the constructs that relation
   admits, on the primitives pmap names, with no handlers and no closures. It holds for any code
   the relation accepts, so it is a theorem about accepted code, not about the lowerer: tying
   the two together is OB-JIT-LOWER-GENERAL. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont.
Import ListNotations.
Module JitLowerStable.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont.
Local Open Scope N_scope.

(* ---------- what writes leave alone ---------- *)
Lemma MEnv_stable : forall fp st st' g rho w, MEnv fp st g rho -> Prot g fp w ->
 (forall a, ~ w a -> slotv st a = slotv st' a) -> MEnv fp st' g rho.
Proof.
 intros fp st st' g rho w M P A x s L. destruct (M x s L) as (v & v' & H1 & H2 & H3).
 exists v, v'. repeat split; auto. rewrite <- A; auto. eapply P; eauto.
Qed.
Lemma DoneR_stable : forall c fp st st' w vs os, DoneR c fp st vs os -> Forall (o_safe fp w) os ->
 (forall a, ~ w a -> slotv st a = slotv st' a) -> DoneR c fp st' vs os.
Proof.
 intros c fp st st' w vs os D. induction D; intros F A; [constructor|]. inversion F; subst.
 econstructor; eauto. destruct o; cbn in *; [rewrite <- A; auto|auto].
Qed.
Lemma ArgsAt_stable : forall st st' a0 vs, ArgsAt st a0 vs ->
 (forall a, a0 <= a -> a < a0 + N.of_nat (List.length vs) -> slotv st a = slotv st' a) -> ArgsAt st' a0 vs.
Proof.
 intros st st' a0 vs D. induction D; intros A; [constructor|]. econstructor; eauto.
 - rewrite <- A; eauto; cbn [List.length]; lia.
 - apply IHD. intros b B1 B2. apply A; cbn [List.length]; lia.
Qed.
Lemma loc_range : forall ms i n t, Forall (fun m => n + 2 <= snd m < t) ms ->
 loc ms i = i \/ (n + 2 <= loc ms i < t).
Proof.
 induction ms as [|[s u] ms IH]; intros i n t F; cbn; [auto|].
 inversion F; subst. destruct (N.eqb s i); [right; auto|eapply IH; eauto].
Qed.
Lemma ParamAt_stable : forall fp st st' ms i vs, ParamAt fp st ms i vs ->
 (forall j, i <= j -> j < i + N.of_nat (List.length vs) -> slotv st (fp + loc ms j) = slotv st' (fp + loc ms j)) ->
 ParamAt fp st' ms i vs.
Proof.
 intros fp st st' ms i vs D. induction D; intros A; [constructor|]. econstructor; eauto.
 - rewrite <- A; eauto; cbn [List.length]; lia.
 - apply IHD. intros j J1 J2. apply A; cbn [List.length]; lia.
Qed.

Theorem K_stable :
 (forall c fp st cs w o r k, KD c fp st cs w o r k -> forall st',
    (forall a, ~ w a -> slotv st a = slotv st' a) -> KD c fp st' cs w o r k) /\
 (forall c fp st cs w gd l r k, TK c fp st cs w gd l r k -> forall st',
    (forall a, ~ w a -> slotv st a = slotv st' a) -> TK c fp st' cs w gd l r k) /\
 (forall c fp st cs w dst r k, KC c fp st cs w dst r k -> forall st',
    (forall a, ~ w a -> slotv st a = slotv st' a) -> KC c fp st' cs w dst r k) /\
 (forall fp st cs k, RK fp st cs k -> forall st',
    (forall a, a < fp -> slotv st a = slotv st' a) -> RK fp st' cs k).
Proof.
 apply K_mut; intros;
 try (match goal with
      | H : Sub ?w ?w1, A : forall a, ~ ?w a -> _ |- _ =>
        assert (A1 : forall a, ~ w1 a -> slotv st a = slotv st' a) by (intros q0 N0; apply A; intro X0; apply N0; apply H; auto)
      end).
 - eapply KD_ret; try eassumption. apply H. intros a L. apply H0. intro X. apply s in X. cbn in X. lia.
 - eapply KD_jump; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_label; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_let; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_lett; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_test; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_prim; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KD_call; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
   eapply ArgsAt_stable; [eassumption|]. intros x X1 X2. apply H0. intro W0. apply s0 in W0. cbn in W0.
   rewrite rev_length in X2. subst. lia.
 - eapply KD_tail; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
   + eapply ParamAt_stable; [eassumption|]. intros j J1 J2. apply H0. intro W0. apply s0 in W0. cbn in W0.
     rewrite rev_length in J2.
     assert (J3 : 2 <= j < s) by (subst; lia).
     match goal with HL : forall j0, 2 <= j0 < s -> _ |- _ => destruct (HL j J3) as [E|[E1 E2]] end;
     rewrite ?E in *; destruct W0; subst; lia.
   + apply H. intros a L. apply H0. intro X. apply s0 in X. cbn in X. destruct X; lia.
 - eapply TK_if; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_cond; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_and; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_andr; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_or; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_orr; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_jump; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_label; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply TK_value; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - eapply KC_ret; try eassumption. apply H. intros a L. apply H0. intro X. apply s in X. cbn in X. lia.
 - eapply KC_slot; try eassumption; try (match goal with IH : forall st0, (forall a, _ -> slotv ?st a = slotv st0 a) -> _ |- _ => eapply IH; eassumption end); try (eapply MEnv_stable; eassumption); try (eapply DoneR_stable; eassumption).
 - constructor.
 - eapply RK_call; try eassumption. apply H. intros x X. apply H0. destruct (N.lt_ge_cases x fp) as [Lt|Ge]; [auto|].
   exfalso. apply X. apply a0. lia.
Qed.
Definition KD_stable := proj1 K_stable.
Definition TK_stable := proj1 (proj2 K_stable).
Definition KC_stable := proj1 (proj2 (proj2 K_stable)).
Definition RK_stable := proj2 (proj2 (proj2 K_stable)).
End JitLowerStable.
