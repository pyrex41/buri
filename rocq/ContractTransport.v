(* E2E-08 worked example, transported to the captured evaluator. The pure
   instance of the map contract (ContractExample) is a klambda.shen program in
   the KL-PURE-1 subset: the definition table ds holds map, and the main term
   applies it to a doubling closure and an integer-list literal. Its total
   correctness contract is derived in the calculus for the KLambda
   translation and then carried, by the E2E-07 theorems
   (KLambdaEvaluatorExtended.klambda_refines_ext and
   KLambdaEvaluatorComplete.klambda_complete), to the verdicts of the actual
   captured shen/klambda.shen (KLambdaEvaluatorCapture.program) run by the
   Native model:

   * contract_verdict_sound: at every budget and fuel, a returned value of the
     captured buri.eval is either budget exhaustion or [returned v] with v
     the doubled list -- never a raise, never unsupported;
   * contract_verdict_exists: there is a budget bound beyond which, for all
     large enough fuel, buri.eval returns exactly that [returned v].

   Both are universal theorems over every integer list. They inherit the open
   obligations of E2E-07 (the Chez guard of buri.evaluate is not involved:
   these are statements about buri.eval; Chez-to-Native simulation,
   E2E07-NATIVE, remains open). The mutable-counter instance cannot be
   transported: KL-PURE-1 has no set/value/absvector (CONTRACT-TRANSPORT-MUT). *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory Native
 KLambdaEvaluatorCapture KLambdaEvaluatorPrimitives KLambdaEvaluatorRefinement KLambdaEvaluatorGlobal
 KLambdaEvaluatorExtended KLambdaEvaluatorComplete ContractLogic ContractPrims ContractExample.
Import ListNotations.
Module ContractTransport.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 ContractLogic.ContractLogic ContractPrims.ContractPrims ContractExample.ContractExample.
Module C := KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module Pr := KLambdaEvaluatorPrimitives.KLambdaEvaluatorPrimitives.
Module R := KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.
Module G := KLambdaEvaluatorGlobal.KLambdaEvaluatorGlobal.
Module X := KLambdaEvaluatorExtended.KLambdaEvaluatorExtended.
Module K := KLambdaEvaluatorComplete.KLambdaEvaluatorComplete.

(* ---------- the klambda.shen program ---------- *)
Definition ds : list G.defn := [("map", ["f"; "xs"], map_term)].
Definition dbl_term : C.term := C.TLambda "x" (C.TPrim "+" [C.TVar "x"; C.TVar "x"]).
Definition main_term (l : list Z) : C.term :=
 C.TApply (C.TApply (C.TGlobal "map") dbl_term) (C.TLit (rlist l)).

Lemma data_rlist : forall l, Pr.data (rlist l).
Proof. induction l; cbn; auto. Qed.
Lemma tr_rlist : forall l, R.tr_rv (rlist l) = ilist l.
Proof. induction l as [|z l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.
Lemma ds_ok : X.ds_ok ds.
Proof. repeat constructor; try discriminate; cbn; repeat split; reflexivity. Qed.
Lemma main_sub2 : forall l, X.sub2 (main_term l).
Proof. intro l; cbn. repeat split; try reflexivity. apply data_rlist. Qed.

(* ---------- the pure instance of the map contract ---------- *)
Definition pinv (s : store) := map_bound s /\ base_prims s.
Definition pstep (s0 s1 : store) := s1 = s0.
Lemma pstep_ok : forall s0 s1, pinv s0 -> pstep s0 s1 -> pinv s1 /\ gfuns s1 = gfuns s0.
Proof. intros s0 s1 I ->; auto. Qed.
Lemma pinv_bound : forall s, pinv s -> map_bound s /\ base_prims s.
Proof. auto. Qed.

Section Pure.
Variable P : profile.
Variable RP : resource -> Prop.
Hypothesis PO : policy_ok P RP.
Definition GP := map_spec P RP dbl pstep pinv :: Gx P RP.
Lemma GP_valid : forall n, ctx_at P RP Total n GP.
Proof. exact (map_ctx_valid P RP dbl pstep pinv pstep_ok pinv_bound PO). Qed.

Lemma dbl_spec : fspec P RP dbl pstep pinv (VLam xn (ECall plusn [EVar xn; EVar xn]) []).
Proof.
 intros z s0 (Mb & (_ & _ & _ & _ & Pp)).
 eapply (appj_sound P RP PO Total (Gx P RP)); [apply Gx_valid|]. apply aj_lam.
 eapply r_conseq.
 { eapply d_prim with (s0 := s0) (p := PAdd) (vs := [VNum (NInt z); VNum (NInt z)]);
     [cbn; tauto|repeat constructor|discriminate|exact Pp|reflexivity|reflexivity]. }
 { pre_ok. }
 { intros v s t (-> & -> & ->). repeat split. }
 { exn_ok. }
Qed.

Definition pure_post (l : list Z) : post := fun v s t => v = ilist (map dbl l) /\ t = [].

Lemma main_pure_deriv : forall l s0, map_bound s0 -> base_prims s0 ->
 deriv P RP Total GP (fun s => s = s0) [] (R.tr (main_term l)) (pure_post l) nothing.
Proof.
 intros l s0 Mb Bp. pose proof Bp as (_ & _ & _ & Pk & _).
 cbn [R.tr main_term dbl_term map].
 eapply r_conseq.
 { eapply d_app1 with (fv := VPartial mapn [VLam xn (ECall plusn [EVar xn; EVar xn]) []]) (s1 := s0).
   - eapply d_app1 with (fv := VPartial mapn []) (s1 := s0); [|apply d_atom; reflexivity|].
     + apply r_call0. apply aj_partial. intros s ->. exists (FUser map_params map_body). split; [exact Mb|split; [cbn; lia|repeat split]].
     + apply aj_partial. intros s ->. exists (FUser map_params map_body). split; [exact Mb|split; [cbn; lia|repeat split]].
   - apply (lit_ok P RP GP); [cbn [GP Gx In]; tauto|exact Pk].
   - apply (aj_ctx P RP Total GP (map_spec P RP dbl pstep pinv) [VLam xn (ECall plusn [EVar xn; EVar xn]) []]);
       [left; reflexivity|].
     intros s ->. split; [|split; [intros v s' t' H; exact H|intros x s' t' []]].
     exists (VLam xn (ECall plusn [EVar xn; EVar xn]) []), l. split; [reflexivity|split; [split; assumption|apply dbl_spec]]. }
 { pre_ok. }
 { intros v s t (fv & l' & Ev & -> & _ & ->). injection Ev as _ El. apply ilist_inj in El. subst l'. split; reflexivity. }
 { exn_ok. }
Qed.

Theorem main_pure_total : forall l s0, map_bound s0 -> base_prims s0 ->
 triple P RP Total (fun s => s = s0) [] (R.tr (main_term l)) (pure_post l) nothing.
Proof. intros l s0 Mb Bp. exact (deriv_sound P RP PO Total GP _ _ _ _ _ GP_valid (main_pure_deriv l s0 Mb Bp)). Qed.
End Pure.

(* ---------- the E2E-07 premises imply the contract's store premises ---------- *)
Lemma store_premises : forall s, R.prims s -> X.defs s ds -> map_bound s /\ base_prims s.
Proof.
 intros s Hp Hd. split.
 - unfold map_bound, mapn. rewrite (Hd "map"). reflexivity.
 - unfold base_prims; repeat split; apply Hp; cbn; tauto.
Qed.

(* The resource policy for a pinned E2E-07 profile: no stack bound (pure2),
   heap failure admitted exactly when the profile has a heap bound. *)
Definition rp (P : profile) (r : resource) := r = RHeap /\ heap_limit P <> None.
Lemma rp_ok : forall P, X.pure2 P -> policy_ok P (rp P).
Proof.
 intros P HP. split; intro N.
 - exfalso; apply N; exact (proj1 (proj1 HP)).
 - split; [reflexivity|exact N].
Qed.

Definition start (l : list Z) (s : store) := Cfg (Eval [] (R.tr (main_term l))) [] s.

(* KLambda-level total correctness for every E2E-07 profile and store. *)
Theorem pure_run : forall P s l, X.pure2 P -> R.prims s -> X.defs s ds ->
 exists n t o, R.krun P n (start l s) tt = VDone t o /\ match o with
 | Normal v => v = ilist (map dbl l) /\ t = []
 | ResourceOut r => rp P r
 | _ => False end.
Proof.
 intros P s l HP Hs Hd. destruct (store_premises s Hs Hd) as [Mb Bp].
 destruct (total_run P (rp P) unit R.env_none R.still _ [] (R.tr (main_term l)) (pure_post l) nothing s tt
   (main_pure_total P (rp P) (rp_ok P HP) l s Mb Bp) eq_refl) as (n & t & o & Rn & Ho).
 exists n, t, o; split; [exact Rn|].
 destruct o; cbn in Ho; try contradiction; [destruct Ho as (s' & Hq); exact Hq|destruct Ho as (s' & [])|exact Ho].
Qed.

Lemma krun_det : forall P c n m a b, R.krun P n c tt = a -> R.krun P m c tt = b ->
 KLMetatheory.KLMetatheory.decided a -> KLMetatheory.KLMetatheory.decided b -> a = b.
Proof.
 intros P c n m a b Ra Rb Da Db. unfold R.krun in *.
 pose proof (KLMetatheory.KLMetatheory.run_monotone unit R.env_none R.quiet R.still P n (n + m) c tt ltac:(lia)) as M1.
 pose proof (KLMetatheory.KLMetatheory.run_monotone unit R.env_none R.quiet R.still P m (n + m) c tt ltac:(lia)) as M2.
 rewrite Ra in M1; rewrite Rb in M2. rewrite <- (M1 Da), <- (M2 Db). reflexivity.
Qed.

(* Transported soundness: every value the captured buri.eval returns for the
   example, at any budget z and any Native fuel n, is budget exhaustion or the
   doubled list. A raise or an unsupported verdict is impossible. *)
Theorem contract_verdict_sound : forall l n z r,
 Native.Native.run n C.program "kl:buri.eval"
   [G.enc_defs ds; C.enc_term (main_term l); C.enc_env []; Native.Native.Integer z] = Native.Native.Returned r ->
 r = C.enc_verdict C.WBudget \/ exists v, r = C.enc_verdict (C.WRet v) /\ R.tr_rv v = ilist (map dbl l).
Proof.
 intros l n z r H.
 destruct (X.klambda_refines_ext ds n (main_term l) z r ds_ok (main_sub2 l) H) as (w & -> & _ & Gw).
 pose proof (X.defs_store_ok ds) as [Hs Hd].
 specialize (Gw X.pure2_profile (X.defs_store ds) X.pure2_profile_ok Hs Hd).
 destruct (pure_run X.pure2_profile (X.defs_store ds) l X.pure2_profile_ok Hs Hd) as (n1 & t & o & R1 & Ho).
 destruct w as [v|msg| |].
 - right. exists v; split; [reflexivity|]. destruct Gw as [m Rm].
   pose proof (krun_det _ _ _ _ _ _ R1 Rm I I) as E. injection E as -> ->. destruct Ho as [Hv _]; exact Hv.
 - exfalso. destruct Gw as (x & m & _ & Rm). pose proof (krun_det _ _ _ _ _ _ R1 Rm I I) as E.
   injection E as -> ->. exact Ho.
 - left; reflexivity.
 - exfalso. destruct Gw as [m Rm]. pose proof (krun_det _ _ _ _ _ _ R1 Rm I I) as E. discriminate.
Qed.

(* Transported existence: beyond a budget bound, the captured buri.eval
   returns [returned v] with v the doubled list, for all large enough fuel. *)
Theorem contract_verdict_exists : forall l, exists m, forall z, (Z.of_nat m < z)%Z ->
 exists v n0, (forall n, n0 <= n -> Native.Native.run n C.program "kl:buri.eval"
     [G.enc_defs ds; C.enc_term (main_term l); C.enc_env []; Native.Native.Integer z] =
     Native.Native.Returned (C.enc_verdict (C.WRet v))) /\
   R.tr_rv v = ilist (map dbl l).
Proof.
 intro l. pose proof (X.defs_store_ok ds) as [Hs Hd].
 destruct (pure_run X.pure2_profile (X.defs_store ds) l X.pure2_profile_ok Hs Hd) as (n1 & t & o & R1 & Ho).
 destruct o as [v'| | | | |]; cbn in Ho; try contradiction.
 2:{ destruct Ho as [_ N]; exfalso; apply N; reflexivity. }
 destruct Ho as [-> ->]. exists n1. intros z Lz.
 destruct (K.klambda_complete ds (main_term l) X.pure2_profile (X.defs_store ds) n1 (Normal (ilist (map dbl l)))
   ds_ok (main_sub2 l) X.pure2_profile_ok Hs Hd R1 z Lz) as (w & n0 & Rn & Hw).
 destruct w as [v|msg| |]; try contradiction.
 - exists v, n0; split; [exact Rn|]. injection Hw as Hw; symmetry; exact Hw.
 - destruct Hw as (x & E & _); discriminate.
Qed.
End ContractTransport.
