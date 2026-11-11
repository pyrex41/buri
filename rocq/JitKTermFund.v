(* Shen/JIT Phase 2: KRef's fundamental property, outright (r1-kref-fund, option A).
   The statements fund_gen_statement, fundamental_statement, KRef_refl_statement,
   store_refl_statement, adequacy_statement, call_preservation_src_statement and the
   compatibility statements compat_trap, compat_app and compat_call are JitKTerm.v's; this file
   re-opens Section Equiv (and Section Compose) with JitKTerm.v's Variables and proves each of them
   with no hypothesis beyond its own premises. No Definition here changes a JitKTerm statement.

   - fund_step: D_wf -> fund_below k -> fund_at k, by structural induction on the expression
     (JitKTermFv.expr_ind'), one case per constructor:
       literals (ERel_sval), a variable (ERel_sval when it is in scope, ERel_throw_both when it is
       bound on neither side: both raise XUnboundVar), let (ERel_let: the body at j < k from
       fund_below k, at k from the induction hypothesis), if, and, or, cond, type (the ERel_ lemmas), trap
       (ERel_trap with JitKTermCompatCtl.AppExn_fb k), defun (ERel_defun, from D_wf), lambda and
       freeze (JitKTermCompatClo.compat_lambda_lt, compat_freeze_lt), dynamic application
       (JitKTermCompatClo.compat_app_lt with JitKTermPrim.prim_compat, whose = case rests on
       JitEqBudgetCore.eq_budget_closed) and a named call (JitKTermCompatCall.compat_call_refl_lt).
       Lambda, freeze, application and call need only fund_below k: their subterms run one target
       step later, at indices below k.
   - fund_gen: fund_gen_statement, by JitKTermFv.fund_gen_of_step (induction on the index).
   - fundamental: fundamental_statement. EnvRelAll relates the two environments pointwise with
     equal names, so they are related on g := map fst rho0 and every other name is bound on
     neither side, which is fund_below's scope condition.
   - KRef_refl: KRef_refl_statement, from fund_gen at the index and fv_scope_of_scoped.
   - compat_trap, compat_app, compat_call: the three compatibility statements that the earlier
     files proved only from fund_gen_statement, now outright.
   - store_refl, adequacy, call_preservation_src: JitKTermGround's store_refl_of_fundamental and
     adequacy_of_fundamental and JitKTermCompose's call_preservation_src_of_fundamental, applied to
     fundamental. store_ok is carried beside SRel as the statements' own premise (store_refl's
     store_ok s, adequacy's store_ok s): SRel does not give it (JitKTermBase.SRel_lok_refuted).

   KRef's treatment of the = budget is unchanged: = is prim_compat's case, from
   eq_budget_closed over the world-reachable cells; there is no fallback.
   No axiom, no Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKTerm JitKTermGround JitKTermBase JitKTermCompatClo JitKTermPrim JitKTermCompatCtl JitKTermCompatCall JitKTermFv.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKTermFund.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKTerm.JitKTerm
 JitKTermGround.JitKTermGround JitKTermBase.JitKTermBase.
Module B := JitBytecode.JitBytecode.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Notation VRel := (JitKTerm.JitKTerm.VRel sealed D).
Notation ERel := (JitKTerm.JitKTerm.ERel sealed D).
Notation KRef := (JitKTerm.JitKTerm.KRef sealed D).
Notation D_wf := (JitKTerm.JitKTerm.D_wf sealed D).
Notation EnvRelAll := (JitKTerm.JitKTerm.EnvRelAll sealed D).
Notation fund_below := (JitKTerm.JitKTerm.fund_below sealed D).
Notation fund_gen_statement := (JitKTerm.JitKTerm.fund_gen_statement sealed D).
Notation fundamental_statement := (JitKTerm.JitKTerm.fundamental_statement sealed D).
Notation KRef_refl_statement := (JitKTerm.JitKTerm.KRef_refl_statement sealed D).
Notation store_refl_statement := (JitKTerm.JitKTerm.store_refl_statement sealed D).
Notation adequacy_statement := (JitKTerm.JitKTerm.adequacy_statement sealed D).
Notation compat_trap_statement := (JitKTerm.JitKTerm.compat_trap_statement sealed D).
Notation compat_app_statement := (JitKTerm.JitKTerm.compat_app_statement sealed D).
Notation compat_call_statement := (JitKTerm.JitKTerm.compat_call_statement sealed D).
Notation fund_at := (JitKTermFv.JitKTermFv.fund_at sealed D).
Notation EnvRel_mono := (JitKTermBase.JitKTermBase.EnvRel_mono sealed D).
Notation fv_scope := JitKTermFv.JitKTermFv.fv_scope.

(* ======================= the step: fund_below k gives fund_at k ======================= *)
Lemma fund_below_le : forall k j, (j <= k)%nat -> fund_below k -> fund_below j.
Proof. intros k j L H i Li. apply H. lia. Qed.

Lemma ERel_lit : forall k w rho0 rho e v, lit_val e = Some v -> ERel k w rho0 e rho e.
Proof.
 intros k w rho0 rho e v H.
 eapply JitKTermCompatCtl.JitKTermCompatCtl.ERel_sval;
  [apply JitKTermCompatCtl.JitKTermCompatCtl.lit_sval; exact H
  |apply JitKTermCompatCtl.JitKTermCompatCtl.lit_sval; exact H
  |eapply JitKTermCompatCtl.JitKTermCompatCtl.VRel_lit; exact H].
Qed.

Lemma ERel_var : forall k w g rho0 rho x, EnvRel_with (VRel k) w g rho0 rho -> fv_scope g rho0 rho (EVar x) ->
 ERel k w rho0 (EVar x) rho (EVar x).
Proof.
 intros k w g rho0 rho x HE F. destruct (F x (or_introl eq_refl)) as [I|[N0 N]].
 - destruct (HE x I) as (v0 & v & E0 & E & HV).
   eapply JitKTermCompatCtl.JitKTermCompatCtl.ERel_sval; [exact E0|exact E|exact HV].
 - apply (JitKTermCompatCtl.JitKTermCompatCtl.ERel_throw_both sealed D) with (x := XUnboundVar x).
   + intros K0 s0. cbn. rewrite N0. reflexivity.
   + intros K s. cbn. rewrite N. reflexivity.
Qed.

(* The bound value of a let, or of anything else that extends both environments by x: the body
   at every j <= k under every larger world, from fund_below k below k and from the structural
   hypothesis at k. *)
Lemma body_at : forall k w g rho0 rho x b,
 fund_below k ->
 (forall w g rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> fv_scope g rho0 rho b ->
    ERel k w rho0 b rho b) ->
 EnvRel_with (VRel k) w g rho0 rho ->
 (forall v0 v, fv_scope (x :: g) ((x, v0) :: rho0) ((x, v) :: rho) b) ->
 forall j w' v0 v, (j <= k)%nat -> wext w w' -> VRel j w' v0 v -> ERel j w' ((x, v0) :: rho0) b ((x, v) :: rho) b.
Proof.
 intros k w g rho0 rho x b Fb IH HE Fs j w' v0 v L W HV.
 assert (HE' : EnvRel_with (VRel j) w' (x :: g) ((x, v0) :: rho0) ((x, v) :: rho)).
 { apply JitKTermCompatCtl.JitKTermCompatCtl.env_cons; [eapply EnvRel_mono; [exact L|exact W|exact HE]|exact HV]. }
 destruct (Nat.eq_dec j k) as [->|Ne].
 - apply (IH w' (x :: g)); [apply W|exact HE'|apply Fs].
 - apply (Fb j ltac:(lia) w' (x :: g)); [apply W|exact HE'|apply Fs].
Qed.

Ltac ih H Ww HE := eapply H; [exact Ww|exact HE|assumption].

Theorem fund_step : D_wf -> forall k, fund_below k -> fund_at k.
Proof.
 intros Dw k Fb w g rho0 rho e. revert w g rho0 rho.
 induction e as [n|t|s|bo| |x|x b IHb|x a b IHa IHb|c a b IHc IHa IHb|a b IHa IHb|a b IHa IHb
   |cl IHcl|a b IHa IHb|b IHb|b IHb|f ps b IHb|h args IHh IHargs|f args IHargs]
   using JitKTermFv.JitKTermFv.expr_ind'; intros w g rho0 rho Ww HE Fs.
 - eapply ERel_lit; reflexivity.
 - eapply ERel_lit; reflexivity.
 - eapply ERel_lit; reflexivity.
 - eapply ERel_lit; reflexivity.
 - eapply ERel_lit; reflexivity.
 - eapply ERel_var; [exact HE|exact Fs].
 - eapply JitKTermCompatClo.JitKTermCompatClo.compat_lambda_lt; [exact Fb|exact Ww|exact HE|exact Fs].
 - apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_let.
   + apply (IHa w g); [exact Ww|exact HE|eapply JitKTermFv.JitKTermFv.fv_scope_let_bound; exact Fs].
   + eapply body_at; [exact Fb|exact IHb|exact HE|].
     intros v0 v. eapply JitKTermFv.JitKTermFv.fv_scope_let_body; exact Fs.
 - destruct (JitKTermFv.JitKTermFv.fv_scope_if _ _ _ _ _ _ Fs) as (Fc & Fa & Fb').
   apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_if; [ih IHc Ww HE|ih IHa Ww HE|ih IHb Ww HE].
 - destruct (JitKTermFv.JitKTermFv.fv_scope_and _ _ _ _ _ Fs) as (Fa & Fb').
   apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_and; [ih IHa Ww HE|ih IHb Ww HE].
 - destruct (JitKTermFv.JitKTermFv.fv_scope_or _ _ _ _ _ Fs) as (Fa & Fb').
   apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_or; [ih IHa Ww HE|ih IHb Ww HE].
 - apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_cond.
   pose proof (JitKTermFv.JitKTermFv.fv_scope_cond _ _ _ _ Fs) as Fcl. clear Fs.
   induction cl as [|[c b] cl IH]; [constructor|].
   inversion IHcl as [|? ? [Hc Hb] IHcl']; subst. inversion Fcl as [|? ? [Fc Fb'] Fcl']; subst.
   constructor; [cbn [fst snd]; split; [ih Hc Ww HE|ih Hb Ww HE]|apply IH; assumption].
 - destruct (JitKTermFv.JitKTermFv.fv_scope_trap _ _ _ _ _ Fs) as (Fa & Fb').
   apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_trap;
    [exact (JitKTermCompatCtl.JitKTermCompatCtl.AppExn_fb sealed D k Fb)|ih IHa Ww HE|ih IHb Ww HE].
 - eapply JitKTermCompatClo.JitKTermCompatClo.compat_freeze_lt; [exact Fb|exact Ww|exact HE|exact Fs].
 - apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_type. ih IHb Ww HE.
 - apply JitKTermCompatCtl.JitKTermCompatCtl.ERel_defun. exact Dw.
 - eapply JitKTermCompatClo.JitKTermCompatClo.compat_app_lt;
    [exact Fb|exact (JitKTermPrim.JitKTermPrim.prim_compat sealed D)|exact Ww|exact HE|exact Fs].
 - eapply JitKTermCompatCall.JitKTermCompatCall.compat_call_refl_lt; [exact Fb|exact Ww|exact HE|exact Fs].
Qed.

(* ======================= the fundamental property ======================= *)
Theorem fund_gen : fund_gen_statement.
Proof. apply JitKTermFv.JitKTermFv.fund_gen_of_step. exact fund_step. Qed.

Theorem fund_at_all : D_wf -> forall k, fund_at k.
Proof. intros Dw k. apply JitKTermFv.JitKTermFv.fund_below_at. apply fund_gen. exact Dw. Qed.

Lemma name_dec : forall a b : name, {a = b} + {a <> b}.
Proof.
 intros a b. destruct (text_eqb a b) eqn:E; [left; apply text_eqb_eq; exact E|right].
 intros H. subst. rewrite text_eqb_refl in E. discriminate.
Defined.

(* EnvRelAll relates the two environments on their (common) names, and binds every other name on
   neither side. *)
Lemma EnvRelAll_scope : forall k w rho0 rho, EnvRelAll k w rho0 rho ->
 EnvRel_with (VRel k) w (map fst rho0) rho0 rho /\
 forall y, ~ In y (map fst rho0) -> lookup y rho0 = None /\ lookup y rho = None.
Proof.
 intros k w rho0 rho H. induction H as [|p0 p r0 r Hp F [IHE IHN]].
 - split; [intros y []|intros y _; split; reflexivity].
 - destruct p0 as [x0 v0], p as [x v]. destruct Hp as [Ex HV]. cbn [fst snd] in Ex, HV. subst x0.
   split.
   + intros y I. cbn [lookup]. destruct (text_eqb y x) eqn:E.
     * exists v0, v. split; [reflexivity|split; [reflexivity|exact HV]].
     * destruct I as [I|I]; [cbn [fst] in I; subst; rewrite text_eqb_refl in E; discriminate|].
       exact (IHE y I).
   + intros y N. cbn [lookup]. destruct (text_eqb y x) eqn:E.
     * apply text_eqb_eq in E. subst. exfalso. apply N. left. reflexivity.
     * apply IHN. intros I. apply N. right. exact I.
Qed.

Theorem fundamental : fundamental_statement.
Proof.
 intros k w rho0 rho e Dw Ww HA. destruct (EnvRelAll_scope k w rho0 rho HA) as [HE HN].
 apply (fund_at_all Dw k w (map fst rho0) rho0 rho e Ww HE).
 intros y _. destruct (in_dec name_dec y (map fst rho0)) as [I|N]; [left; exact I|right; apply HN, N].
Qed.

Theorem KRef_refl : KRef_refl_statement.
Proof.
 intros g e Dw S k w rho0 rho Ww HE.
 apply (fund_at_all Dw k w g rho0 rho e Ww HE). apply JitKTermFv.JitKTermFv.fv_scope_of_scoped. exact S.
Qed.

(* ======================= the compatibility statements, outright ======================= *)
Theorem compat_trap : compat_trap_statement.
Proof. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_trap_of_gen sealed D fund_gen). Qed.

Theorem compat_app : compat_app_statement.
Proof.
 exact (JitKTermCompatClo.JitKTermCompatClo.compat_app_of_fund sealed D fund_gen
   (JitKTermPrim.JitKTermPrim.prim_compat sealed D)).
Qed.

Theorem compat_call : compat_call_statement.
Proof. exact (JitKTermCompatCall.JitKTermCompatCall.compat_call_of_fund sealed D fund_gen). Qed.

(* ======================= store reflexivity and adequacy ======================= *)
Theorem store_refl : store_refl_statement.
Proof. exact (JitKTermGround.JitKTermGround.store_refl_of_fundamental sealed D fundamental). Qed.

Theorem adequacy : adequacy_statement.
Proof. exact (JitKTermGround.JitKTermGround.adequacy_of_fundamental sealed D fundamental). Qed.

End Equiv.
End JitKTermFund.
