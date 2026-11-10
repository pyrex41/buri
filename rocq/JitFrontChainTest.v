(* Shen/JIT Phase 2, F00: a synthetic test of JitFrontCheck's composition contract.
   Two toy source-anti-reduction rules, each with a closed rule_sound:
   - rule_if_true, if-true elimination: (if true A B) on the source becomes A, then rec on the
     same target node (JitKRefBase.ERel_anti_if);
   - rule_let_lit, let-of-literal substitution in its smallest case: (let X L X), L a literal,
     becomes L, then rec on the same target node (JitKRefBase.ERel_anti_let, then one silent source
     step to the same value on both forms: obs_same_next). The general substitution of L for X in
     any body is NOT a rule here: its soundness needs a substitution lemma under closures, which no
     file proves.
   The pair chain_src / chain_tgt needs both rules at the root: if-true turns the source into the
   let, whose rec call (fuel - 1) then fires the let rule. fchk accepts it with both rules and
   rejects it when either is removed; each verdict is closed by vm_compute. chain_kref turns the
   acceptance into KRef under FrontHyps.
   Synthetic: these rules are not lower.shen's and gate no stage 0 count. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitFrontCheck.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontChainTest.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKRef.JitKRef JitFrontCheck.JitFrontCheck.

Definition is_lit (e : expr) : bool := match lit_val e with Some _ => true | None => false end.

Definition rule_if_true : rule := fun rec g e0 e => match e0 with
 | EIf (EBool true) a _ => rec g a e
 | _ => false end.

Definition rule_let_lit : rule := fun rec g e0 e => match e0 with
 | ELet x a (EVar y) => text_eqb x y && is_lit a && rec g a e
 | _ => false end.

Section Toy.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation ObsT := (JitKRef.JitKRef.ObsT sealed).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation rule_sound := (JitFrontCheck.rule_sound sealed D).

Lemma sval_lit : forall rho a v, lit_val a = Some v -> JitKRefBase.JitKRefBase.sval rho a = Some v.
Proof. intros rho a v H. destruct a; cbn in *; congruence. Qed.

Theorem rule_if_true_sound : rule_sound rule_if_true.
Proof.
 intros rec Hr g e0 e E. destruct e0; try discriminate. destruct e0_1; try discriminate.
 destruct b; try discriminate. cbn in E. intros k w rho0 rho W HE.
 apply (JitKRefBase.JitKRefBase.ERel_anti_if sealed D k w (EBool true) e0_2 e0_3 true rho0 rho e); [reflexivity|].
 exact (Hr g e0_2 e E k w rho0 rho W HE).
Qed.

(* Two running configurations with the same next move, continuation and store, the second not a
   final value: whatever the second can do, the first can. *)
Lemma srun_same_next : forall c0 c0', next_r R P c0 = next_r R P c0' -> running_state c0 = true ->
 running_state c0' = true -> kont c0 = kont c0' -> mem c0 = mem c0' ->
 forall t cf, srun c0' t cf -> (cf = c0' /\ t = []) \/ srun c0 t cf.
Proof.
 intros c0 c0' E R0 R1 Ek Em t cf H. inversion H as [|c l c1 t' c2 St H' Eq1 Eq2 Eq3]; subst; [left; split; reflexivity|right].
 assert (St' : step_r R P c0 l c1).
 { destruct St as [c c' E'|c q kk r E'|c r x Rs Rx].
   - apply step_r_tau. rewrite E. exact E'.
   - apply (step_r_io R P c0 q kk r). rewrite E. exact E'.
   - rewrite <- Ek, <- Em. apply (step_r_resource R P c0 r x); assumption. }
 econstructor; [exact St'|exact H'].
Qed.

Lemma obs_same_next : forall k w c0 c0' c, next_r R P c0 = next_r R P c0' -> running_state c0 = true ->
 running_state c0' = true -> kont c0 = kont c0' -> mem c0 = mem c0' ->
 (forall v s, c0' <> Cfg (Ret v) [] s) -> ObsT k w c0' c -> ObsT k w c0 c.
Proof.
 intros k w c0 c0' c E R0 R1 Ek Em Nr H n t c' L Hr. destruct (H n t c' L Hr) as (A & B & C).
 split; [|split].
 - intros v s Ev. destruct (A v s Ev) as (v0 & s0 & w' & S0 & X).
   destruct (srun_same_next c0 c0' E R0 R1 Ek Em _ _ S0) as [[Eq _]|S1].
   + exfalso. exact (Nr v0 s0 (eq_sym Eq)).
   + exists v0, s0, w'. split; assumption.
 - intros x s Ex. destruct (B x s Ex) as (s0 & w' & S0 & X).
   destruct (srun_same_next c0 c0' E R0 R1 Ek Em _ _ S0) as [[Eq _]|S1].
   + rewrite <- Eq in R1. discriminate.
   + exists s0, w'. split; assumption.
 - intros why Ew. destruct (C why Ew) as (c1 & why0 & S0 & X).
   destruct (srun_same_next c0 c0' E R0 R1 Ek Em _ _ S0) as [[Eq Et]|S1].
   + subst c1 t. exists c0, why0. split; [constructor|rewrite E; exact X].
   + exists c1, why0. split; assumption.
Qed.

Theorem rule_let_lit_sound : rule_sound rule_let_lit.
Proof.
 intros rec Hr g e0 e E. destruct e0; try discriminate. destruct e0_2; try discriminate.
 cbn in E. apply andb_true_iff in E as [E Ea]. apply andb_true_iff in E as [Ex El].
 apply text_eqb_eq in Ex. subst x0. unfold is_lit in El.
 destruct (lit_val e0_1) as [v|] eqn:Lv; [|discriminate].
 intros k w rho0 rho W HE. pose proof (Hr g e0_1 e Ea k w rho0 rho W HE) as He.
 apply (JitKRefBase.JitKRefBase.ERel_anti_let sealed D k w x e0_1 (EVar x) v rho0 rho e); [apply sval_lit; exact Lv|].
 unfold JitKRef.JitKRef.ERel, JitKRef.JitKRef.ERel_with in *.
 intros j L w' Ww K0 K HK s0 s HS. specialize (He j L w' Ww K0 K HK s0 s HS).
 apply (obs_same_next j w' _ (Cfg (Eval rho0 e0_1) K0 s0)); try reflexivity.
 - destruct e0_1; cbn in Lv; try discriminate; injection Lv as <-; cbn; rewrite text_eqb_refl; reflexivity.
 - intros v' s' Eq. discriminate.
 - exact He.
Qed.

Lemma toy_rules_sound : Forall rule_sound [rule_if_true; rule_let_lit].
Proof. constructor; [exact rule_if_true_sound|constructor; [exact rule_let_lit_sound|constructor]]. Qed.
End Toy.

Definition x_name : name := of_string "x".
(* (if true (let x 5 x) 0) against 5. *)
Definition chain_src : expr := EIf (EBool true) (ELet x_name (ENum (NInt 5)) (EVar x_name)) (ENum (NInt 0)).
Definition chain_tgt : expr := ENum (NInt 5).

Theorem chain_accepted : fchk [rule_if_true; rule_let_lit] 4 [] chain_src chain_tgt = true.
Proof. vm_compute. reflexivity. Qed.
Theorem chain_rejected_without_if : fchk [rule_let_lit] 4 [] chain_src chain_tgt = false.
Proof. vm_compute. reflexivity. Qed.
Theorem chain_rejected_without_let : fchk [rule_if_true] 4 [] chain_src chain_tgt = false.
Proof. vm_compute. reflexivity. Qed.
(* Removing a rule rejects the pair at every fuel, not only at 4. *)
Theorem chain_rejected_without_if_any_fuel : forall n, fchk [rule_let_lit] n [] chain_src chain_tgt = false.
Proof. intros [|n]; [reflexivity|]. destruct n; reflexivity. Qed.
Theorem chain_rejected_without_let_any_fuel : forall n, fchk [rule_if_true] n [] chain_src chain_tgt = false.
Proof. intros [|n]; [reflexivity|]. destruct n as [|n]; [reflexivity|]. destruct n; reflexivity. Qed.

Theorem chain_kref : forall sealed D, FrontHyps sealed D -> KRef sealed D [] chain_src chain_tgt.
Proof.
 intros sealed D FH. apply (fchk_sound sealed D FH _ (toy_rules_sound sealed D) 4). exact chain_accepted.
Qed.
End JitFrontChainTest.
