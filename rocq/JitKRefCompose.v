(* Shen/JIT Phase 2: KRef's composition with call_preservation (K00 split of JitLowerEquiv.v).
   EndsSrc and call_preservation_src_statement are in JitKRef.v (see its file map); the proofs here
   are JitLowerEquiv.v's, moved. This file re-opens Section Equiv and Section Compose with the same
   Variables and local notations, and one local abbreviation per JitKRef or JitKRefGround constant
   that takes `sealed`, `D`, `E` or `pt`, so that after the Sections close each theorem has exactly
   its old type and argument order. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefCompose.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKRef.JitKRef
 JitKRefGround.JitKRefGround.
Module B := JitBytecode.JitBytecode.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
(* The JitKRef and JitKRefGround constants as they read inside Section Equiv. *)
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
Notation D_bodies := (JitKRef.JitKRef.D_bodies D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation D_compiled := (JitKRef.JitKRef.D_compiled D).
Notation D_compiled_spec_statement := (JitKRef.JitKRef.D_compiled_spec_statement D).
Notation eq_budget_statement := (JitKRef.JitKRef.eq_budget_statement sealed).
Notation sealed_stable_statement := (JitKRef.JitKRef.sealed_stable_statement sealed).
Notation storehas_stable_statement := (JitKRef.JitKRef.storehas_stable_statement sealed D).
Notation VRelF_index_statement := (JitKRef.JitKRef.VRelF_index_statement sealed D).
Notation VRel_down_statement := (JitKRef.JitKRef.VRel_down_statement sealed D).
Notation VRel_wext_statement := (JitKRef.JitKRef.VRel_wext_statement sealed D).
Notation ERel_down_statement := (JitKRef.JitKRef.ERel_down_statement sealed D).
Notation VRel_ground_statement := (JitKRef.JitKRef.VRel_ground_statement sealed D).
Notation SRel_ground_statement := (JitKRef.JitKRef.SRel_ground_statement sealed D).
Notation KRel_top_statement := (JitKRef.JitKRef.KRel_top_statement sealed D).
Notation EnvRelAll := (JitKRef.JitKRef.EnvRelAll sealed D).
Notation fundamental_statement := (JitKRef.JitKRef.fundamental_statement sealed D).
Notation KRef_refl_statement := (JitKRef.JitKRef.KRef_refl_statement sealed D).
Notation store_refl_statement := (JitKRef.JitKRef.store_refl_statement sealed D).
Notation compat_lit_statement := (JitKRef.JitKRef.compat_lit_statement sealed D).
Notation compat_var_statement := (JitKRef.JitKRef.compat_var_statement sealed D).
Notation compat_let_statement := (JitKRef.JitKRef.compat_let_statement sealed D).
Notation compat_if_statement := (JitKRef.JitKRef.compat_if_statement sealed D).
Notation compat_and_statement := (JitKRef.JitKRef.compat_and_statement sealed D).
Notation compat_or_statement := (JitKRef.JitKRef.compat_or_statement sealed D).
Notation compat_cond_statement := (JitKRef.JitKRef.compat_cond_statement sealed D).
Notation compat_type_statement := (JitKRef.JitKRef.compat_type_statement sealed D).
Notation compat_trap_statement := (JitKRef.JitKRef.compat_trap_statement sealed D).
Notation compat_lambda_statement := (JitKRef.JitKRef.compat_lambda_statement sealed D).
Notation compat_freeze_statement := (JitKRef.JitKRef.compat_freeze_statement sealed D).
Notation compat_call_statement := (JitKRef.JitKRef.compat_call_statement sealed D).
Notation compat_app_statement := (JitKRef.JitKRef.compat_app_statement sealed D).
Notation compat_defun_statement := (JitKRef.JitKRef.compat_defun_statement sealed D).
Notation KRef_scope_statement := (JitKRef.JitKRef.KRef_scope_statement sealed D).
Notation adequacy_statement := (JitKRef.JitKRef.adequacy_statement sealed D).
Notation srun_nil_Sstar_statement := (JitKRef.JitKRef.srun_nil_Sstar_statement sealed).
Notation D_compiled_spec := (JitKRefGround.JitKRefGround.D_compiled_spec D).
Notation runs_srun := (JitKRefGround.JitKRefGround.runs_srun sealed).
Notation srun_runs := (JitKRefGround.JitKRefGround.srun_runs sealed).
Notation srun_nil_Sstar := (JitKRefGround.JitKRefGround.srun_nil_Sstar sealed).
Notation step_from_ret_top := (JitKRefGround.JitKRefGround.step_from_ret_top sealed).
Notation no_step_from_throw_top := (JitKRefGround.JitKRefGround.no_step_from_throw_top sealed).
Notation VRel_unfold := (JitKRefGround.JitKRefGround.VRel_unfold sealed D).
Notation VRelF_index := (JitKRefGround.JitKRefGround.VRelF_index sealed D).
Notation VBody_partial := (JitKRefGround.JitKRefGround.VBody_partial sealed D).
Notation VBody_ground := (JitKRefGround.JitKRefGround.VBody_ground sealed D).
Notation VRel_ground := (JitKRefGround.JitKRefGround.VRel_ground sealed D).
Notation SRel_with_ground := (JitKRefGround.JitKRefGround.SRel_with_ground D).
Notation SRel_ground := (JitKRefGround.JitKRefGround.SRel_ground sealed D).
Notation SRel_with_wf := (JitKRefGround.JitKRefGround.SRel_with_wf D).
Notation obs_top_throw := (JitKRefGround.JitKRefGround.obs_top_throw sealed).
Notation obs_top_ret := (JitKRefGround.JitKRefGround.obs_top_ret sealed).
Notation KRel_top := (JitKRefGround.JitKRefGround.KRel_top sealed D).
Notation KRel_with_ext := (JitKRefGround.JitKRefGround.KRel_with_ext sealed D).
Notation ERel_with_ext := (JitKRefGround.JitKRefGround.ERel_with_ext sealed D).
Notation vrefl := (JitKRefGround.JitKRefGround.vrefl sealed D).
Notation store_refl_of_fundamental := (JitKRefGround.JitKRefGround.store_refl_of_fundamental sealed D).
Notation adequacy_of_fundamental := (JitKRefGround.JitKRefGround.adequacy_of_fundamental sealed D).
Notation runs := (JitKRef.JitKRef.runs sealed).
Notation runs_0 := (JitKRef.JitKRef.runs_0 sealed).
Notation runs_S := (JitKRef.JitKRef.runs_S sealed).

Section Compose.
Variables (E : B.env) (pt : B.tree (B.prim * nat)).
(* The JitKRef constants of Section Compose as they read inside it. *)
Notation call_preservation_src_statement := (JitKRef.JitKRef.call_preservation_src_statement sealed D E pt).
Notation EndsSrc := (JitKRef.JitKRef.EndsSrc sealed E pt).
Notation ES_ok := (JitKRef.JitKRef.ES_ok sealed E pt).
Notation ES_err := (JitKRef.JitKRef.ES_err sealed E pt).

(* The composition, as an explicit implication from the fundamental property: it is proved here
   that fundamental_statement implies call_preservation_src_statement. The fundamental property is
   NOT proved here. *)
Lemma VR_fo : forall v v', VR v v' -> fo v.
Proof. intros v v' H; induction H; constructor; auto. Qed.

Lemma ArgsAt_fo : forall st a args, ArgsAt st a args -> Forall fo args.
Proof. intros st a args H; induction H; constructor; [eapply VR_fo; eauto|auto]. Qed.

Lemma combine_fo : forall (ps : list name) args, Forall fo args -> Forall (fun p => fo (snd p)) (combine ps args).
Proof.
 induction ps as [|x ps IH]; intros [|v args] H; cbn; try apply Forall_nil.
 inversion H; subst. apply Forall_cons; [exact H2|apply IH; exact H3].
Qed.

Lemma lookup_combine : forall (ps : list name) (args : list value) x,
 List.length ps = List.length args -> In x ps -> exists v, lookup x (combine ps args) = Some v.
Proof.
 induction ps as [|y ps IH]; intros [|v args] x L I; cbn in *; try contradiction; try discriminate.
 destruct (text_eqb x y) eqn:T; [eauto|]. destruct I as [Ex|I].
 - subst. rewrite text_eqb_refl in T. discriminate.
 - apply IH; [lia|exact I].
Qed.

Theorem call_preservation_src_of_fundamental : fundamental_statement -> call_preservation_src_statement.
Proof.
 intros F s m c ps b0 b1 e args n DW K01 K1e HS Hok Cm Cf L En c0 ce.
 pose proof (call_preservation E pt sealed s m c ps e args n Cm Cf L En) as CP. cbv zeta in CP.
 destruct CP as [H|[m1 [HE HT]]]; [left; exact H|right; exists m1; split; [|exact HT]].
 assert (Hfo : Forall (fun p => fo (snd p)) (combine ps args)).
 { apply combine_fo. destruct En as [_ [_ [_ Aa]]]. eapply ArgsAt_fo; exact Aa. }
 assert (Hdom : forall x, In x ps -> exists v, lookup x (combine ps args) = Some v) by (intros; apply lookup_combine; auto).
 destruct (adequacy_of_fundamental F ps b1 e (combine ps args) s DW K1e Hfo Hdom HS Hok) as [A1 B1].
 destruct (adequacy_of_fundamental F ps b0 b1 (combine ps args) s DW K01 Hfo Hdom HS Hok) as [A0 B0].
 destruct HE as [v v' m2 Ss Nf Vr|x l msg tv m2 Ss Nf Lh Xo].
 - apply srun_nil_Sstar in Ss. pose proof (VR_fo _ _ Vr) as Fv.
   destruct (A1 v s Ss Fv) as (s1 & w2 & S1 & W2 & G2).
   destruct (A0 v s1 S1 Fv) as (s0 & w1 & S0 & W1 & G1).
   eapply ES_ok with (s0 := s0) (w := compose_world w1 w2); [apply srun_nil_Sstar; exact S0| | |exact Nf|exact Vr].
   + apply wext_compose_id; assumption.
   + eapply GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact G1|exact G2].
 - apply srun_nil_Sstar in Ss.
   destruct (B1 x s Ss) as (s1 & w2 & S1 & W2 & G2).
   destruct (B0 x s1 S1) as (s0 & w1 & S0 & W1 & G1).
   eapply ES_err with (s0 := s0) (w := compose_world w1 w2); [apply srun_nil_Sstar; exact S0| | |exact Nf|exact Lh|exact Xo].
   + apply wext_compose_id; assumption.
   + eapply GStore_trans; [exact (proj2 W1)|exact (proj2 W2)|exact G1|exact G2].
Qed.
End Compose.
End Equiv.
End JitKRefCompose.
