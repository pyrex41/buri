(* Shen/JIT Phase 2: KRef's ground proofs (K00 split of JitLowerEquiv.v). The statements are in
   JitKRef.v (see its file map); the proofs here are JitLowerEquiv.v's, moved. This file re-opens
   Section Equiv with the same Variables and local notations as JitKRef.v, and one local
   abbreviation per JitKRef constant that takes `sealed` or `D`, so that after the Section closes each
   theorem has exactly its old type and argument order. Tactic arguments name the JitKRef constants
   themselves (unfold, cbn), never the abbreviations. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefGround.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKRef.JitKRef.
Module B := JitBytecode.JitBytecode.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
(* The JitKRef constants as they read inside JitKRef's Section Equiv. *)
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
Notation runs := (JitKRef.JitKRef.runs sealed).
Notation runs_0 := (JitKRef.JitKRef.runs_0 sealed).
Notation runs_S := (JitKRef.JitKRef.runs_S sealed).

(* ======================= proofs (Phase B, part B) ======================= *)
(* Proved here: the premises' specifications, the ground relation's lemmas, KRel_top, and, as
   explicit implications from fundamental_statement, store reflexivity and adequacy. The
   fundamental property itself and the compatibility lemmas are NOT proved here. *)

(* --- premise specifications --- *)
Theorem fresh_ok_spec : fresh_ok_spec_statement.
Proof.
 intros ns es. unfold fresh_ok. rewrite forallb_forall. split.
 - intros H e x Ie Ix. specialize (H e Ie). rewrite forallb_forall in H.
   apply negb_true_iff. apply H. exact Ix.
 - intros H e Ie. rewrite forallb_forall. intros x Ix. apply negb_true_iff. eapply H; eauto.
Qed.

Theorem no_keyword_binders_spec : no_keyword_binders_spec_statement.
Proof.
 intros e. unfold no_keyword_binders. rewrite forallb_forall. split.
 - intros H x I. apply negb_true_iff. apply H. exact I.
 - intros H x I. apply negb_true_iff. apply H. exact I.
Qed.

Theorem D_compiled_spec : D_compiled_spec_statement.
Proof.
 intros cs H f ps b I. unfold JitKRef.JitKRef.D_compiled in H. rewrite forallb_forall in H.
 specialize (H _ I). cbn in H. destruct (lookup f cs) as [c|]; [|discriminate].
 exists c. split; [reflexivity|]. apply check_fn_sound. exact H.
Qed.

(* --- runs --- *)
Lemma runs_srun : forall n c t c', runs n c t c' -> srun c t c'.
Proof. intros n c t c' H; induction H; [constructor|econstructor; eauto]. Qed.

Lemma srun_runs : forall c t c', srun c t c' -> exists n, runs n c t c'.
Proof.
 intros c t c' H; induction H as [c|c l c1 t c2 St _ [n IH]]; [exists 0%nat; constructor|].
 exists (S n). econstructor; eauto.
Qed.

Theorem srun_nil_Sstar : srun_nil_Sstar_statement.
Proof.
 intros c c'. split.
 - intro H. remember [] as t eqn:Et. unfold JitKRef.JitKRef.srun in H.
   induction H as [c|c l c1 t c2 St H IH]; [constructor|].
   destruct l as [|ev]; [|discriminate]. econstructor; [exact St|]. apply IH. exact Et.
 - intro H. induction H as [c|c c1 c2 St H IH]; [constructor|].
   change (@nil event) with (trace_of Tau ++ []). econstructor; [exact St|exact IH].
Qed.

Lemma step_from_ret_top : forall v s l c1, step_r R P (Cfg (Ret v) [] s) l c1 ->
 l = Tau /\ exists x r, resource_exn R r = Some x /\ c1 = Cfg (Throw x) [] s.
Proof.
 intros v s l c1 H. inversion H; subst; cbn in *; try discriminate.
 split; [reflexivity|]. eauto.
Qed.

Lemma no_step_from_throw_top : forall x s l c1, step_r R P (Cfg (Throw x) [] s) l c1 -> False.
Proof. intros x s l c1 H. inversion H; subst; cbn in *; discriminate. Qed.

(* --- worlds --- *)
Lemma wext_refl : forall w, wf_world w -> wext w w.
Proof. intros w H. split; [intros a A; exact A|exact H]. Qed.

Lemma In_compose : forall w1 w2 a b c, In (a, b) w1 -> In (b, c) w2 -> In (a, c) (compose_world w1 w2).
Proof.
 intros w1 w2 a b c I1 I2. unfold compose_world. apply in_flat_map. exists (a, b). split; [exact I1|].
 apply in_map_iff. exists (b, c). split; [reflexivity|]. apply filter_In. split; [exact I2|]. cbn. apply Nat.eqb_refl.
Qed.

Lemma In_compose_inv : forall w1 w2 a c, In (a, c) (compose_world w1 w2) -> exists b, In (a, b) w1 /\ In (b, c) w2.
Proof.
 intros w1 w2 a c I. unfold compose_world in I. apply in_flat_map in I as [[a' b] [I1 I2]].
 apply in_map_iff in I2 as [[b' c'] [E I3]]. cbn in E. inversion E; subst.
 apply filter_In in I3 as [I3 B]. cbn in B. apply Nat.eqb_eq in B. subst. eauto.
Qed.

Lemma nodup_fst_uniq : forall (w : world) a b b', NoDup (map fst w) -> In (a, b) w -> In (a, b') w -> b = b'.
Proof.
 induction w as [|[x y] w IH]; cbn; intros a b b' N I1 I2; [contradiction|].
 inversion N as [|? ? NI N']; subst.
 destruct I1 as [E1|I1]; destruct I2 as [E2|I2].
 - inversion E1; inversion E2; subst; reflexivity.
 - inversion E1; subst. exfalso. apply NI. apply in_map_iff. exists (a, b'). auto.
 - inversion E2; subst. exfalso. apply NI. apply in_map_iff. exists (a, b). auto.
 - eapply IH; eauto.
Qed.

Lemma nodup_snd_uniq : forall (w : world) a a' b, NoDup (map snd w) -> In (a, b) w -> In (a', b) w -> a = a'.
Proof.
 induction w as [|[x y] w IH]; cbn; intros a a' b N I1 I2; [contradiction|].
 inversion N as [|? ? NI N']; subst.
 destruct I1 as [E1|I1]; destruct I2 as [E2|I2].
 - inversion E1; inversion E2; subst; reflexivity.
 - inversion E1; subst. exfalso. apply NI. apply in_map_iff. exists (a', b). auto.
 - inversion E2; subst. exfalso. apply NI. apply in_map_iff. exists (a, b). auto.
 - eapply IH; eauto.
Qed.

Lemma filter_fst_nil : forall (w : world) b, ~ In b (map fst w) -> filter (fun q => Nat.eqb b (fst q)) w = [].
Proof.
 induction w as [|[x y] w IH]; cbn; intros b N; [reflexivity|].
 destruct (Nat.eqb b x) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply N; left; reflexivity|].
 apply IH. intro I; apply N; right; exact I.
Qed.

Lemma filter_fst_small : forall (w : world) b, NoDup (map fst w) ->
 filter (fun q => Nat.eqb b (fst q)) w = [] \/ exists q, filter (fun q => Nat.eqb b (fst q)) w = [q].
Proof.
 induction w as [|[x y] w IH]; cbn; intros b N; [left; reflexivity|].
 inversion N as [|? ? NI N']; subst.
 destruct (Nat.eqb b x) eqn:E.
 - apply Nat.eqb_eq in E; subst. right. exists (x, y). rewrite filter_fst_nil; [reflexivity|exact NI].
 - apply IH. exact N'.
Qed.

Lemma wf_compose : forall w1 w2, wf_world w1 -> wf_world w2 -> wf_world (compose_world w1 w2).
Proof.
 intros w1 w2 [F1 S1] [F2 S2]. induction w1 as [|[a b] w1 IH]; [split; constructor|].
 cbn in F1, S1. inversion F1 as [|? ? NF F1']; inversion S1 as [|? ? NS S1']; subst.
 destruct (IH F1' S1') as [IF IS].
 unfold compose_world. cbn [flat_map]. fold (compose_world w1 w2). cbn [fst snd].
 destruct (filter_fst_small w2 b F2) as [E|[q E]]; rewrite E; cbn [map app].
 - split; assumption.
 - assert (Iq : In q (filter (fun q => Nat.eqb b (fst q)) w2)) by (rewrite E; left; reflexivity).
   apply filter_In in Iq as [Iq Bq]. apply Nat.eqb_eq in Bq. destruct q as [b' c]. cbn in Bq. subst b'.
   split; cbn; constructor; try assumption.
   + intro I. apply in_map_iff in I as [[a' c'] [Ea I]]. cbn in Ea. subst a'.
     apply In_compose_inv in I as [b'' [J1 _]]. apply NF. apply in_map_iff. exists (a, b''). auto.
   + intro I. apply in_map_iff in I as [[a' c'] [Ec I]]. cbn in Ec. subst c'.
     apply In_compose_inv in I as [b'' [J1 J2]].
     assert (b'' = b) by (eapply nodup_snd_uniq; [exact S2|exact J2|exact Iq]). subst b''.
     apply NS. apply in_map_iff. exists (a', b). auto.
Qed.

Lemma wext_compose_id : forall s w1 w2, wext (id_world s) w1 -> wext (id_world s) w2 ->
 wext (id_world s) (compose_world w1 w2).
Proof.
 intros s w1 w2 [I1 W1] [I2 W2]. split; [|apply wf_compose; assumption].
 intros [a b] I. assert (a = b) as <-.
 { unfold id_world in I. apply in_map_iff in I as [l [E _]]. inversion E; reflexivity. }
 eapply In_compose; [apply I1|apply I2]; exact I.
Qed.

Lemma id_world_wf : forall s, wf_world (id_world s).
Proof.
 intro s. unfold id_world, wf_world. rewrite !map_map. cbn. rewrite !map_id. split; apply seq_NoDup.
Qed.

Lemma id_world_in : forall s l, (l < List.length (heap s))%nat -> In (l, l) (id_world s).
Proof. intros s l L. unfold id_world. apply in_map_iff. exists l. split; [reflexivity|]. apply in_seq. lia. Qed.

Lemma id_world_inv : forall s a b, In (a, b) (id_world s) -> a = b /\ (a < List.length (heap s))%nat.
Proof.
 intros s a b I. unfold id_world in I. apply in_map_iff in I as [l [E I]]. inversion E; subst.
 apply in_seq in I. split; [reflexivity|lia].
Qed.

(* --- the ground relation --- *)
Lemma same_id_trans : forall w1 w2 r0 r1 r, same_id w1 r0 r1 -> same_id w2 r1 r ->
 same_id (compose_world w1 w2) r0 r.
Proof.
 intros w1 w2 r0 r1 r H1 H2. unfold same_id in *.
 destruct (closure_id r0), (closure_id r1), (closure_id r); try contradiction; auto.
 eapply In_compose; eauto.
Qed.

Lemma GVal_partial : forall w f0 f as0 as1,
 GVal w (VPartial f0 as0) (VPartial f as1) <-> f0 = f /\ Forall2 (GVal w) as0 as1.
Proof.
 intros w f0 f as0 as1. cbn [GVal]. split; intros [E H]; split; try exact E.
 - revert as1 H; induction as0 as [|x0 as0 IH]; intros [|x as1] H; cbn in H; try contradiction; [constructor|].
   destruct H as [H1 H2]. constructor; [exact H1|apply IH; exact H2].
 - induction H; cbn; tauto.
Qed.

Lemma GVal_trans : GVal_trans_statement.
Proof.
 intros w1 w2 a b c W1 W2 H1 H2. split; [|apply wf_compose; assumption].
 revert b c H1 H2. induction a using value_rect'; intros b' c' H1 H2;
  destruct b'; try (cbn in H1; contradiction); destruct c'; try (cbn in H2; contradiction).
 11: { apply GVal_partial. apply GVal_partial in H1 as [E1 F1]. apply GVal_partial in H2 as [E2 F2].
   split; [congruence|]. revert args0 args1 F1 F2. induction H as [|x l Px Pl IH]; intros l1 l2 F1 F2.
   + inversion F1; subst. inversion F2; subst. constructor.
   + inversion F1; subst. inversion F2; subst. constructor; eauto. }
 all: cbn in *; try (subst; reflexivity); auto.
 - destruct H1, H2. split; eauto.
 - eapply In_compose; eauto.
 - eapply same_id_trans; eauto.
 - eapply same_id_trans; eauto.
Qed.

Lemma Forall2_trans_gen : forall {A B C} (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) (R3 : A -> C -> Prop) l1 l2 l3,
 (forall a b c, R1 a b -> R2 b c -> R3 a c) -> Forall2 R1 l1 l2 -> Forall2 R2 l2 l3 -> Forall2 R3 l1 l3.
Proof.
 intros A B C R1 R2 R3 l1 l2 l3 T F1. revert l3. induction F1; intros l3 F2; inversion F2; subst; constructor; eauto.
Qed.

Theorem GStore_trans : GStore_trans_statement.
Proof.
 intros w1 w2 s0 s1 s W1 W2 [G1 [V1 H1]] [G2 [V2 H2]]. split; [congruence|split].
 - eapply Forall2_trans_gen; [|exact V1|exact V2].
   intros [x0 a] [x1 b] [x c] [E1 A] [E2 B]; cbn in *. split; [congruence|]. eapply GVal_trans; eauto.
 - intros l0 l I. apply In_compose_inv in I as [b [I1 I2]].
   destruct (H1 _ _ I1) as (c0 & c1 & N0 & N1 & F1). destruct (H2 _ _ I2) as (c1' & c & N1' & N & F2).
   rewrite N1 in N1'. inversion N1'; subst. exists c0, c. split; [exact N0|split; [exact N|]].
   eapply Forall2_trans_gen; [|exact F1|exact F2]. intros a b' c'' A B. eapply GVal_trans; eauto.
Qed.

Lemma GVal_fo : forall w v0 v, fo v -> GVal w v0 v -> v0 = v.
Proof.
 intros w v0 v F. revert v0. induction F; intros v0 G; destruct v0; cbn in G; try contradiction; subst; try reflexivity.
 destruct G as [G1 G2]. f_equal; auto.
Qed.

(* --- the index family --- *)
Lemma leb_S_false : forall k, Nat.leb (S k) k = false.
Proof. intro k. apply Nat.leb_gt. lia. Qed.

Lemma VRel_unfold : forall k, VRel k = VBody (match k with O => fun _ _ _ _ => False | S k' => VRelF k' end) k.
Proof.
 intros [|k]; [reflexivity|]. unfold JitKRef.JitKRef.VRel.
 change (VRelF (S k) (S k)) with (if Nat.leb (S k) k then VRelF k (S k) else VBody (VRelF k) (S k)).
 rewrite leb_S_false. reflexivity.
Qed.

Theorem VRelF_index : VRelF_index_statement.
Proof.
 intro k. induction k as [|k IH]; intros j L.
 - assert (j = 0%nat) by lia. subst. reflexivity.
 - change (VRelF (S k) j) with (if Nat.leb j k then VRelF k j else VBody (VRelF k) (S k)).
   destruct (Nat.leb j k) eqn:E.
   + apply Nat.leb_le in E. apply IH. exact E.
   + apply Nat.leb_gt in E. assert (j = S k) by lia. subst.
     unfold JitKRef.JitKRef.VRel. change (VRelF (S k) (S k)) with (if Nat.leb (S k) k then VRelF k (S k) else VBody (VRelF k) (S k)).
     rewrite leb_S_false. reflexivity.
Qed.

Lemma VBody_partial : forall V k w f0 f as0 as1,
 VBody V k w (VPartial f0 as0) (VPartial f as1) <-> f0 = f /\ Forall2 (VBody V k w) as0 as1.
Proof.
 intros V k w f0 f as0 as1. cbn [JitKRef.JitKRef.VBody]. split; intros [E H]; split; try exact E.
 - revert as1 H; induction as0 as [|x0 as0 IH]; intros [|x as1] H; cbn in H; try contradiction; [constructor|].
   destruct H as [H1 H2]. constructor; [exact H1|apply IH; exact H2].
 - induction H; cbn; tauto.
Qed.

Lemma VBody_ground : forall V k w v0 v, VBody V k w v0 v -> GVal w v0 v.
Proof.
 intros V k w v0. induction v0 using value_rect'; intros v' H'; destruct v'; try (cbn in H'; contradiction).
 11: { apply GVal_partial. apply VBody_partial in H' as [E F]. split; [exact E|].
   revert args0 F. induction H as [|x l Px Pl IH]; intros l1 F; inversion F; subst; constructor; auto. }
 all: cbn in *; auto; try (destruct H'; auto; fail).
Qed.

Theorem VRel_ground : VRel_ground_statement.
Proof. intros k w v0 v H. rewrite VRel_unfold in H. eapply VBody_ground; exact H. Qed.

Lemma SRel_with_ground : forall (V1 : world -> value -> value -> Prop) w s0 s,
 (forall a b, V1 w a b -> GVal w a b) -> SRel_with V1 w s0 s -> GStore w s0 s.
Proof.
 intros V1 w s0 s G (W & H0 & H1 & Gf & Gv & Hp). split; [exact Gf|split].
 - eapply Forall2_impl; [|exact Gv]. intros [x a] [y b] [E A]; split; auto.
 - intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. repeat split; auto.
   eapply Forall2_impl; [|exact F]. auto.
Qed.

Theorem SRel_ground : SRel_ground_statement.
Proof. intros k w s0 s H. eapply SRel_with_ground; [|exact H]. intros a b; apply VRel_ground. Qed.

Lemma SRel_with_wf : forall (V1 : world -> value -> value -> Prop) w s0 s, SRel_with V1 w s0 s -> wf_world w.
Proof. intros V1 w s0 s H; apply H. Qed.

(* --- the empty continuation --- *)
Lemma obs_top_throw : forall j w x s0 s, wf_world w -> GStore w s0 s ->
 ObsT j w (Cfg (Throw x) [] s0) (Cfg (Throw x) [] s).
Proof.
 intros j w x s0 s W G n t c' L Hr. inversion Hr as [c|n' c l c1 t' c2 St Hr']; subst.
 - split; [|split].
   + intros v s' E; discriminate.
   + intros x' s' E. inversion E; subst. exists s0, w. split; [constructor|split; [apply wext_refl; exact W|exact G]].
   + intros why N. cbn in N. discriminate.
 - exfalso. eapply no_step_from_throw_top; exact St.
Qed.

Lemma obs_top_ret : forall j w v0 v s0 s, wf_world w -> GVal w v0 v -> GStore w s0 s ->
 ObsT j w (Cfg (Ret v0) [] s0) (Cfg (Ret v) [] s).
Proof.
 intros j w v0 v s0 s W Gv G n t c' L Hr. inversion Hr as [c|n' c l c1 t' c2 St Hr']; subst.
 - split; [|split].
   + intros v' s' E. inversion E; subst. exists v0, s0, w. split; [constructor|split; [apply wext_refl; exact W|auto]].
   + intros x s' E; discriminate.
   + intros why N. cbn in N. discriminate.
 - destruct (step_from_ret_top _ _ _ _ St) as [-> [x [r [Rx ->]]]].
   inversion Hr' as [c|n'' c l c1 t'' c2 St' _]; subst.
   + split; [|split].
     * intros v' s' E; discriminate.
     * intros x' s' E. inversion E; subst. exists s0, w. split; [|split; [apply wext_refl; exact W|exact G]].
       change (trace_of Tau ++ []) with (trace_of Tau ++ @nil event). econstructor; [|constructor].
       eapply (step_r_resource _ _ (Cfg (Ret v0) [] s0) r); [reflexivity|exact Rx].
     * intros why N. cbn in N. discriminate.
   + exfalso. eapply no_step_from_throw_top; exact St'.
Qed.

Theorem KRel_top : KRel_top_statement.
Proof.
 intros k w _ j L w' [I W]. split.
 - intros v0 v s0 s HV HS. rewrite (VRelF_index k j L) in HV, HS.
   apply obs_top_ret; [exact W|apply VRel_ground with (k := j); exact HV|].
   eapply SRel_with_ground; [|exact HS]. intros a b; apply VRel_ground.
 - intros x s0 s HS. rewrite (VRelF_index k j L) in HS.
   apply obs_top_throw; [exact W|]. eapply SRel_with_ground; [|exact HS]. intros a b; apply VRel_ground.
Qed.

(* --- transport between index families --- *)
Lemma KRel_with_ext : forall V V' j w K0 K, (forall i, (i <= j)%nat -> V i = V' i) ->
 KRel_with V j w K0 K -> KRel_with V' j w K0 K.
Proof.
 intros V V' j w K0 K Eq H i L w' Hw. destruct (H i L w' Hw) as [A B].
 rewrite <- (Eq i L). split; assumption.
Qed.

Lemma ERel_with_ext : forall V V' j w r0 e0 r e, (forall i, (i <= j)%nat -> V i = V' i) ->
 ERel_with V j w r0 e0 r e -> ERel_with V' j w r0 e0 r e.
Proof.
 intros V V' j w r0 e0 r e Eq H j' L w' Hw K0 K HK s0 s HS.
 rewrite <- (Eq j' L) in HS. apply H; auto.
 eapply KRel_with_ext; [|exact HK]. intros i Li. symmetry. apply Eq. lia.
Qed.

(* --- reflexivity of values and stores, from the fundamental property --- *)
Section FromFundamental.
Hypothesis F : fundamental_statement.

Lemma same_id_refl : forall n w rho, eok n rho -> (forall l, (l < n)%nat -> In (l, l) w) -> same_id w rho rho.
Proof.
 intros n w rho E H. unfold same_id. destruct rho as [|[kk vv] rr]; cbn; [exact I|].
 destruct vv; try exact I. destruct (text_eqb kk id_key); [|exact I].
 apply H. inversion E; subst. exact H2.
Qed.

Lemma Forall2_refl_env : forall (Q : value -> Prop) (R2 : value -> value -> Prop) (rho : lenv),
 Forall (fun p => Q (snd p)) rho -> (forall v, Q v -> R2 v v) ->
 Forall2 (fun p0 p => fst p0 = fst p /\ R2 (snd p0) (snd p)) rho rho.
Proof. intros Q R2 rho H T. induction H; constructor; auto. Qed.

Lemma vrefl : D_wf -> forall v n k w, wf_world w -> (forall l, (l < n)%nat -> In (l, l) w) -> vok n v -> VRel k w v v.
Proof.
 intros DW v. induction v using value_rect'; intros nb k w W Hw Ok; rewrite VRel_unfold.
 11: { apply VBody_partial. split; [reflexivity|]. cbn in Ok. apply fold_lok in Ok.
   induction H as [|x l Px Pl IH]; [constructor|]. inversion Ok; subst. constructor; [|apply IH; auto].
   rewrite <- (VRel_unfold k). eapply Px; eauto. }
 all: cbn [JitKRef.JitKRef.VBody]; auto; try (apply Hw; exact Ok).
 - cbn in Ok. destruct Ok as [O1 O2].
   split; rewrite <- (VRel_unfold k); [eapply IHv1|eapply IHv2]; eauto.
 - cbn in Ok. apply fold_eok in Ok. split; [eapply same_id_refl; eauto|].
   destruct k as [|k]; [intros j L; lia|].
   intros j L w' [Iw' W'] a0 a A. cbv beta iota in A |- *.
   rewrite (VRelF_index k j ltac:(lia)) in A.
   eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
   apply F; [exact DW|exact W'|]. constructor; [split; [reflexivity|exact A]|].
   clear -H Ok Iw' W' Hw DW. induction H as [|[y u] rr Pu Prr IH]; [constructor|].
   inversion Ok; subst. constructor; [split; [reflexivity|]|apply IH; auto].
   cbn in *. apply (Pu nb); [exact W'|intros l Ll; apply Iw'; apply Hw; exact Ll|assumption].
 - cbn in Ok. apply fold_eok in Ok. split; [eapply same_id_refl; eauto|].
   destruct k as [|k]; [intros j L; lia|].
   intros j L w' [Iw' W']. cbv beta iota.
   eapply ERel_with_ext with (V := VRelF j); [intros i Li; rewrite !VRelF_index by lia; reflexivity|].
   apply F; [exact DW|exact W'|].
   clear -H Ok Iw' W' Hw DW. induction H as [|[y u] rr Pu Prr IH]; [constructor|].
   inversion Ok; subst. constructor; [split; [reflexivity|]|apply IH; auto].
   cbn in *. apply (Pu nb); [exact W'|intros l Ll; apply Iw'; apply Hw; exact Ll|assumption].
Qed.

Theorem store_refl_of_fundamental : store_refl_statement.
Proof.
 intros k s DW HS [Hh Hg]. unfold JitKRef.JitKRef.SRel, JitKRef.JitKRef.SRel_with.
 split; [apply id_world_wf|split; [exact HS|split; [exact HS|split; [reflexivity|split]]]].
 - eapply Forall2_refl_env; [exact Hg|]. intros v Ov. eapply vrefl; [exact DW|apply id_world_wf| |exact Ov].
   intros l L; apply id_world_in; exact L.
 - intros l0 l I. apply id_world_inv in I as [<- L].
   destruct (nth_error (heap s) l0) as [c|] eqn:N; [|apply nth_error_None in N; lia].
   exists c, c. split; [reflexivity|split; [reflexivity|]].
   assert (Oc : lok (List.length (heap s)) c).
   { rewrite Forall_forall in Hh. apply Hh. eapply nth_error_In; exact N. }
   clear -Oc DW F. induction Oc as [|x c Ox Oc IH]; constructor; [|exact IH].
   eapply vrefl; [exact DW|apply id_world_wf| |exact Ox]. intros l L; apply id_world_in; exact L.
Qed.

Lemma fo_vok : forall n v, fo v -> vok n v.
Proof. intros n v H; induction H; cbn; auto. Qed.

Lemma lookup_In : forall x (rho : lenv) v, lookup x rho = Some v -> In (x, v) rho.
Proof.
 induction rho as [|[y u] rho IH]; cbn; intros v E; [discriminate|].
 destruct (text_eqb x y) eqn:T; [apply text_eqb_eq in T; subst; inversion E; subst; left; reflexivity|right; auto].
Qed.

Theorem adequacy_of_fundamental : adequacy_statement.
Proof.
 intros g e0 e rho s DW HK Hfo Hdom HS Hok.
 assert (Main : forall n t c', runs n (Cfg (Eval rho e) [] s) t c' -> ObsT (S n) (id_world s) (Cfg (Eval rho e0) [] s) (Cfg (Eval rho e) [] s)).
 { intros n t c' _. eapply (HK (S n) (id_world s) rho rho (id_world_wf s)).
   - intros x Ix. destruct (Hdom x Ix) as [v Lv]. exists v, v. split; [exact Lv|split; [exact Lv|]].
     eapply vrefl with (n := 0%nat); [exact DW|apply id_world_wf|intros l L; lia|].
     apply fo_vok. apply lookup_In in Lv. rewrite Forall_forall in Hfo. exact (Hfo _ Lv).
   - apply le_n.
   - apply wext_refl, id_world_wf.
   - apply KRel_top, id_world_wf.
   - exact (store_refl_of_fundamental (S n) s DW HS Hok). }
 split.
 - intros v s' Hr Fv. destruct (srun_runs _ _ _ Hr) as [n Hn].
   destruct (Main _ _ _ Hn n [] _ (Nat.lt_succ_diag_r n) Hn) as [A _].
   destruct (A v s' eq_refl) as (v0 & s0 & w' & S0 & Wx & Gv & Gs).
   rewrite (GVal_fo _ _ _ Fv Gv) in S0. exists s0, w'. auto.
 - intros x s' Hr. destruct (srun_runs _ _ _ Hr) as [n Hn].
   destruct (Main _ _ _ Hn n [] _ (Nat.lt_succ_diag_r n) Hn) as [_ [B _]].
   destruct (B x s' eq_refl) as (s0 & w' & S0 & Wx & Gs). exists s0, w'. auto.
Qed.
End FromFundamental.
End Equiv.
End JitKRefGround.
