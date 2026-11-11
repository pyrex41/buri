(* Shen/JIT Phase 2, r1-f-inline (track front): soundness of the sealed-inlining checker of
   JitFrontD (aeq, inl_site, bind_site) against KRef.

   PROVED HERE (no axiom, nothing Admitted; each is in Audit_Jit):
   - aeq_sound : JitFrontD.aeq_sound_statement, for every sealed and D. Alpha-equivalent expressions
     (aeq [] e0 e) refine each other. The proof is first done under Section hypotheses naming
     what it uses from the KRef development (fund_below at every index, prim_compat_statement),
     as aeq_sound_of, and then instantiated with JitKRefFund.fund_step and JitKRefPrim.prim_compat.
     It runs at the ERel level, where the KRef compat cores (JitKRefCompatCtl.ERel_let/if/and/or/
     cond/type/trap, JitKRefCompatClo.lam_core/frz_core/compat_app_core,
     JitKRefCompatCall.compat_call_core) take different binder names on the two sides: the
     KRef-level compat_*_statement forms use one binder for both sides, so they cannot express a
     renaming. The induction is on the index (aeq_below, as fund_below) and inside it on the
     source expression (JitKRefFv.expr_ind'). The environment invariant (REnv) relates the
     source lookup of x and the target lookup of y for every pair var_ok rn accepts with x in
     scope; binder_ok keeps KLPort.id_key out of rn, which is what makes REnv survive entering a
     closure body (REnv_tag: the closure's identity cell is bound to id_key on both sides).

   REFUTED HERE (the statements are FALSE as written; Rocq-checked counterexamples):
   - inline_site_unsound : ~ JitFrontD.inline_site_sound_statement sealed_cx D_cx.
   - bind_site_unsound   : ~ JitFrontD.bind_site_sound_statement sealed_bx D_bx.
   The hole. A frozen argument (EFreeze x) that lower.shen thaws in place (inline-frozen, SFrozen x)
   runs, on the source side, inside the frozen closure, whose environment is tagged: KLPort's
   tagged_env binds the closure identity key id_key to the closure's own new cell. On the target
   side x runs in place, in the caller's environment. inl_eq's checks on x (frozen_free: not a
   fresh or parameter name; hidden: not a target binder on the way) and bind_site's
   `disjoint (K.fv ex) [a1; a2; a3]` say nothing about id_key, so x = (EVar id_key) is accepted
   and reads a different value on each side. With empty environments, the target raises
   (XUnboundVar id_key) after one step (inline) or ten (bind); every source run returns the
   closure's identity vector or raises a resource error (XUser _), never XUnboundVar
   (no_reach_iter, a deterministic-chain invariant over KLPort.step_r, whose only
   nondeterminism is the resource step). The real data is unaffected: id_key is the text
   "\0id" (a NUL byte), which no stage 0 name contains; real_sites_guarded below counts it.
   THE FIX (proposed, not applied: JitFrontD.v is D00's file): reject a frozen argument with
   id_key free, i.e. add `negb (bound (K.fv x) KLPort.id_key)` to inl_eq's SFrozen case (or to
   frozen_free) and to bind_site. inl_site_g and bind_site_g below are inl_site and bind_site
   with that guard on the arguments, as decidable checks; the soundness of the guarded checkers
   is NOT proved here (ledger OB-JIT-FRONT-INLINE).

   No axiom, no Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitKRefFv JitKRefFund JitLowerStage0 JitNorm JitNormStage0 JitFrontD.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontInline.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKRef.JitKRef.
Module F := JitFrontD.JitFrontD.

Lemma text_eqb_sym : forall a b, text_eqb a b = text_eqb b a.
Proof.
 intros a b. destruct (text_eqb a b) eqn:E; destruct (text_eqb b a) eqn:E'; try reflexivity.
 - apply text_eqb_eq in E. subst. rewrite text_eqb_refl in E'. discriminate.
 - apply text_eqb_eq in E'. subst. rewrite text_eqb_refl in E. discriminate.
Qed.

Lemma num_eqb_eq : forall a b, F.num_eqb a b = true -> a = b.
Proof.
 intros [x|x] [y|y] H; cbn in H; try discriminate.
 - apply Z.eqb_eq in H. subst. reflexivity.
 - apply N.eqb_eq in H. subst. reflexivity.
Qed.

(* ======================= aeq: inversion on the list forms ======================= *)
Lemma aeq_call : forall rn f0 f l0 l, F.aeq rn (ECall f0 l0) (ECall f l) = true ->
 f0 = f /\ Forall2 (fun a0 a => F.aeq rn a0 a = true) l0 l.
Proof.
 intros rn f0 f l0. induction l0 as [|a0 l0 IH]; intros [|a l] H; cbn in H;
  apply andb_prop in H as [Ef H]; apply text_eqb_eq in Ef; subst f0; try discriminate.
 - split; [reflexivity|constructor].
 - apply andb_prop in H as [Ha H]. split; [reflexivity|]. constructor; [exact Ha|].
   apply (IH l). cbn. rewrite text_eqb_refl. exact H.
Qed.

Lemma aeq_app : forall rn h0 h l0 l, F.aeq rn (EApp h0 l0) (EApp h l) = true ->
 F.aeq rn h0 h = true /\ Forall2 (fun a0 a => F.aeq rn a0 a = true) l0 l.
Proof.
 intros rn h0 h l0 l H. cbn in H. apply andb_prop in H as [Hh H]. split; [exact Hh|].
 refine (proj2 (aeq_call rn nil nil l0 l _)). cbn. exact H.
Qed.

Lemma aeq_cond : forall rn l0 l, F.aeq rn (ECond l0) (ECond l) = true ->
 Forall2 (fun p0 p => F.aeq rn (fst p0) (fst p) = true /\ F.aeq rn (snd p0) (snd p) = true) l0 l.
Proof.
 intros rn l0. induction l0 as [|[c0 b0] l0 IH]; intros [|[c b] l] H; cbn in H; try discriminate.
 - constructor.
 - apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hc Hb].
   constructor; [split; assumption|]. apply IH. cbn. exact Hr.
Qed.

Lemma forallb_Forall' : forall {A} (p : A -> bool) l, forallb p l = true -> Forall (fun x => p x = true) l.
Proof. intros A p l H. apply Forall_forall. intros x I. exact (proj1 (forallb_forall p l) H x I). Qed.

(* ======================= the renamed environment relation ======================= *)
Section Alpha.
Variables (sealed : list name) (D : list (name * fundef)).
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).
Notation prim_compat_statement := (JitKRef.JitKRef.prim_compat_statement sealed D).

(* The pairs of rn: neither binder is the closure-identity key (aeq checks binder_ok). *)
Definition RnOk (rn : list (name * name)) : Prop := Forall (fun p => F.binder_ok (fst p) (snd p) = true) rn.

(* Every source name x in scope and target name y that var_ok rn pairs are bound to related
   values. Does NOT say anything about names outside g. *)
Definition REnv (k : nat) (w : world) (rn : list (name * name)) (g : list name) (rho0 rho : lenv) : Prop :=
 forall x y, In x g -> F.var_ok rn x y = true ->
  exists v0 v, lookup x rho0 = Some v0 /\ lookup y rho = Some v /\ VRel k w v0 v.

Lemma REnv_mono : forall k j w w' rn g r0 r, (j <= k)%nat -> wext w w' -> REnv k w rn g r0 r -> REnv j w' rn g r0 r.
Proof.
 intros k j w w' rn g r0 r L W H x y I V. destruct (H x y I V) as (v0 & v & E0 & E & HV).
 exists v0, v. split; [exact E0|split; [exact E|]]. eapply JitKRefBase.JitKRefBase.VRel_mono; [exact L|exact W|exact HV].
Qed.

Lemma REnv_cons : forall k w rn g r0 r x y v0 v, REnv k w rn g r0 r -> VRel k w v0 v ->
 REnv k w ((x, y) :: rn) (x :: g) ((x, v0) :: r0) ((y, v) :: r).
Proof.
 intros k w rn g r0 r x y v0 v H HV z y' I V. cbn [F.var_ok] in V. cbn [lookup].
 destruct (text_eqb x z) eqn:Exz.
 - apply text_eqb_eq in Exz. subst z. apply text_eqb_eq in V. subst y'. rewrite !text_eqb_refl.
   exists v0, v. auto.
 - destruct (text_eqb y y') eqn:Eyy; [discriminate|].
   rewrite (text_eqb_sym z x), Exz, (text_eqb_sym y' y), Eyy.
   destruct I as [<-|I]; [rewrite text_eqb_refl in Exz; discriminate|]. exact (H z y' I V).
Qed.

Lemma var_ok_id : forall rn z y, RnOk rn -> F.var_ok rn z y = true -> text_eqb z id_key = text_eqb y id_key.
Proof.
 induction rn as [|[a b] rn IH]; intros z y Ok V; cbn [F.var_ok] in V.
 - apply text_eqb_eq in V. subst. reflexivity.
 - inversion Ok as [|? ? Hab Ok']; subst. cbn [fst snd] in Hab. unfold F.binder_ok in Hab.
   apply andb_prop in Hab as [Ha Hb]. apply negb_true_iff in Ha, Hb.
   destruct (text_eqb a z) eqn:Eaz.
   + apply text_eqb_eq in Eaz. subst z. apply text_eqb_eq in V. subst y. rewrite Ha, Hb. reflexivity.
   + destruct (text_eqb b y); [discriminate|]. exact (IH z y Ok' V).
Qed.

(* Entering a closure body: both sides bind id_key to the closures' identity cells, which the
   world relates; RnOk makes var_ok pair id_key only with itself. *)
Lemma REnv_tag : forall k w rn g r0 r l0 l, RnOk rn -> REnv k w rn g r0 r -> In (l0, l) w ->
 REnv k w rn g ((id_key, VVec l0) :: r0) ((id_key, VVec l) :: r).
Proof.
 intros k w rn g r0 r l0 l Ok H I z y Iz V. cbn [lookup]. pose proof (var_ok_id rn z y Ok V) as Eid.
 rewrite <- Eid. destruct (text_eqb z id_key) eqn:E.
 - exists (VVec l0), (VVec l). split; [reflexivity|split; [reflexivity|]].
   eapply JitKRefCompatClo.JitKRefCompatClo.VRel_vec. exact I.
 - exact (H z y Iz V).
Qed.

(* ======================= aeq is sound, by index and structure ======================= *)
Definition aeq_at (k : nat) : Prop :=
 forall w rn g rho0 rho e0 e, wf_world w -> REnv k w rn g rho0 rho -> RnOk rn ->
  scoped g e0 = true -> F.aeq rn e0 e = true -> ERel k w rho0 e0 rho e.
Definition aeq_below (k : nat) : Prop := forall j, (j < k)%nat -> aeq_at j.

Section Hyps.
(* What the proof takes from the KRef development, named; instantiated below. *)
Hypothesis FB : forall k, fund_below k.
Hypothesis PC : prim_compat_statement.

Lemma below_rel : forall k w rn g rho0 rho e0 e, aeq_below k -> wf_world w -> REnv k w rn g rho0 rho -> RnOk rn ->
 scoped g e0 = true -> F.aeq rn e0 e = true ->
 forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 e0 rho e.
Proof.
 intros k w rn g rho0 rho e0 e AB Ww HE Ok S A j w' L W.
 apply (AB j L w' rn g); [apply W|eapply REnv_mono; [|exact W|exact HE]; lia|exact Ok|exact S|exact A].
Qed.

Theorem aeq_step : forall k, aeq_below k -> aeq_at k.
Proof.
 intros k AB w rn g rho0 rho e0. revert w rn g rho0 rho.
 induction e0 as [n|t|s|bo| |x|x b0 IHb|x a0 b0 IHa IHb|c0 a0 b0 IHc IHa IHb|a0 b0 IHa IHb|a0 b0 IHa IHb
   |cl0 IHcl|a0 b0 IHa IHb|b0 IHb|b0 IHb|f ps b0 IHb|h0 args0 IHh IHargs|f args0 IHargs]
   using JitKRefFv.JitKRefFv.expr_ind'; intros w rn g rho0 rho e Ww HE Ok S A;
   destruct e as [n'|t'|s'|bo'| |y|y b|y a b|c a b|a b|a b|cl|a b|b|b|f' ps' b'|h args|f' args];
   cbn [F.aeq] in A; try discriminate.
 - apply num_eqb_eq in A. subst. eapply JitKRefFund.JitKRefFund.ERel_lit. reflexivity.
 - apply text_eqb_eq in A. subst. eapply JitKRefFund.JitKRefFund.ERel_lit. reflexivity.
 - apply text_eqb_eq in A. subst. eapply JitKRefFund.JitKRefFund.ERel_lit. reflexivity.
 - apply Bool.eqb_prop in A. subst. eapply JitKRefFund.JitKRefFund.ERel_lit. reflexivity.
 - eapply JitKRefFund.JitKRefFund.ERel_lit. reflexivity.
 - cbn [scoped] in S. apply JitKRefFv.JitKRefFv.bound_In in S.
   destruct (HE x y S A) as (v0 & v & E0 & E & HV).
   eapply JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval; [exact E0|exact E|exact HV].
 - (* lambda *)
   apply andb_prop in A as [Bo A]. cbn [scoped] in S.
   apply JitKRefCompatClo.JitKRefCompatClo.lam_core. intros j w' l0 l a0 a Lj W I HA.
   apply (AB j Lj w' ((x, y) :: rn) (x :: g)); [apply W| |constructor; [exact Bo|exact Ok]|exact S|exact A].
   apply REnv_cons; [|exact HA]. apply REnv_tag; [exact Ok| |exact I].
   eapply REnv_mono; [|exact W|exact HE]. lia.
 - (* let *)
   apply andb_prop in A as [A Ab]. apply andb_prop in A as [Bo Aa].
   cbn [scoped] in S. apply andb_prop in S as [Sa Sb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_let; [eapply IHa; eassumption|].
   intros j w' v0 v L W HV.
   assert (HE' : REnv j w' ((x, y) :: rn) (x :: g) ((x, v0) :: rho0) ((y, v) :: rho)).
   { apply REnv_cons; [eapply REnv_mono; [exact L|exact W|exact HE]|exact HV]. }
   assert (Ok' : RnOk ((x, y) :: rn)) by (constructor; [exact Bo|exact Ok]).
   destruct (Nat.eq_dec j k) as [->|Ne].
   + eapply IHb; [apply W|exact HE'|exact Ok'|exact Sb|exact Ab].
   + apply (AB j ltac:(lia) w' ((x, y) :: rn) (x :: g)); [apply W|exact HE'|exact Ok'|exact Sb|exact Ab].
 - apply andb_prop in A as [A Ab]. apply andb_prop in A as [Ac Aa].
   cbn [scoped] in S. apply andb_prop in S as [S Sb]. apply andb_prop in S as [Sc Sa].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_if; [eapply IHc|eapply IHa|eapply IHb]; eassumption.
 - apply andb_prop in A as [Aa Ab]. cbn [scoped] in S. apply andb_prop in S as [Sa Sb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_and; [eapply IHa|eapply IHb]; eassumption.
 - apply andb_prop in A as [Aa Ab]. cbn [scoped] in S. apply andb_prop in S as [Sa Sb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_or; [eapply IHa|eapply IHb]; eassumption.
 - (* cond *)
   pose proof (aeq_cond rn cl0 cl A) as Acl.
   rewrite JitKRefFv.JitKRefFv.scoped_cond in S. apply forallb_Forall' in S.
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_cond. clear A.
   revert cl Acl. induction cl0 as [|[c0 b0] cl0 IH]; intros l Acl; inversion Acl as [|p0 p l0' l' Hp Fr]; subst; [constructor|].
   inversion IHcl as [|? ? [Hc Hb] IHcl']; subst. inversion S as [|? ? Sp S']; subst.
   cbn [fst snd] in Hp, Hc, Hb, Sp. apply andb_prop in Sp as [Sc Sb]. destruct Hp as [Hpc Hpb].
   constructor; [split; [eapply Hc|eapply Hb]; eassumption|]. apply IH; assumption.
 - (* trap *)
   apply andb_prop in A as [Aa Ab]. cbn [scoped] in S. apply andb_prop in S as [Sa Sb].
   apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_trap;
    [exact (JitKRefCompatCtl.JitKRefCompatCtl.AppExn_fb sealed D k (FB k))|eapply IHa|eapply IHb]; eassumption.
 - (* freeze *)
   cbn [scoped] in S. apply JitKRefCompatClo.JitKRefCompatClo.frz_core. intros j w' l0 l Lj W I.
   apply (AB j Lj w' rn g); [apply W| |exact Ok|exact S|exact A].
   apply REnv_tag; [exact Ok| |exact I]. eapply REnv_mono; [|exact W|exact HE]. lia.
 - (* type *)
   cbn [scoped] in S. apply JitKRefCompatCtl.JitKRefCompatCtl.ERel_type. eapply IHb; eassumption.
 - (* application *)
   destruct (aeq_app rn h0 h args0 args A) as [Ah Aargs]. cbn [scoped] in S. apply andb_prop in S as [Sh Sargs].
   apply forallb_Forall' in Sargs.
   apply JitKRefCompatClo.JitKRefCompatClo.compat_app_core; [exact (FB k)|exact PC| |].
   + eapply below_rel; eassumption.
   + clear A IHargs. induction Aargs as [|a0 a l0 l Ha Fa IH]; constructor; inversion Sargs as [|? ? Sa Sargs']; subst.
     * eapply below_rel; eassumption.
     * apply IH. exact Sargs'.
 - (* named call *)
   destruct (aeq_call rn f f' args0 args A) as [<- Aargs]. cbn [scoped] in S. apply forallb_Forall' in S.
   apply JitKRefCompatCall.JitKRefCompatCall.compat_call_core; [exact (FB k)|exact PC|].
   clear A IHargs. induction Aargs as [|a0 a l0 l Ha Fa IH]; constructor; inversion S as [|? ? Sa S']; subst.
   + eapply below_rel; eassumption.
   + apply IH. exact S'.
Qed.

Theorem aeq_all : forall k, aeq_at k.
Proof.
 assert (B : forall k, aeq_below k).
 { induction k as [|k IH]; intros j L; [lia|]. destruct (Nat.eq_dec j k) as [->|Ne].
   - apply aeq_step. exact IH.
   - apply IH. lia. }
 intros k. apply (B (S k)). lia.
Qed.

Theorem aeq_sound_of : F.aeq_sound_statement sealed D.
Proof.
 intros g e0 e Dw S A k w rho0 rho Ww HE.
 apply (aeq_all k w [] g rho0 rho e0 e Ww); [|constructor|exact S|exact A].
 intros x y I V. cbn [F.var_ok] in V. apply text_eqb_eq in V. subst y. exact (HE x I).
Qed.
End Hyps.
End Alpha.

(* The instantiation: fund_below at every index (JitKRefFund.fund_step, which needs D_wf, the
   statement's own premise) and prim_compat (JitKRefPrim). *)
Theorem aeq_sound : forall sealed D, F.aeq_sound_statement sealed D.
Proof.
 intros sealed D g e0 e Dw.
 apply (aeq_sound_of sealed D
   (JitKRefFv.JitKRefFv.fund_below_all sealed D (JitKRefFund.JitKRefFund.fund_step sealed D Dw))
   (JitKRefPrim.JitKRefPrim.prim_compat sealed D) g e0 e Dw).
Qed.

(* ======================= the counterexamples: deterministic source chains ======================= *)
Section Chain.
Variable sealed : list name.
Notation R := (jit_rules sealed).
Notation P := jit_profile.

(* iter i c: the configuration after i machine (next_r) tau moves from c. *)
Fixpoint iter (n : nat) (c : config) : config := match n with
 | O => c
 | S n => let c1 := iter n c in match next_r R P c1 with MTau c' => c' | _ => c1 end end.

Definition is_tau (m : move) : bool := match m with MTau _ => true | _ => false end.
Definition is_final (m : move) : bool := match m with MFinal _ => true | _ => false end.
Definition no_trap (k : list frame) : bool := forallb (fun f => match f with KTrap _ _ => false | _ => true end) k.
Definition not_throw (c : config) : bool := match ctl c with Throw _ => false | _ => true end.

(* The first N machine moves from c0 are taus, the N-th configuration is final, no configuration
   on the way is a raise, and no continuation on the way holds a trap frame. *)
Definition chain_ok (N : nat) (c0 : config) : bool :=
 forallb (fun i => is_tau (next_r R P (iter i c0)) && no_trap (kont (iter i c0)) && not_throw (iter i c0)) (seq 0 N)
 && is_final (next_r R P (iter N c0)) && no_trap (kont (iter N c0)) && not_throw (iter N c0).

Lemma chain_at : forall N c0 i, chain_ok N c0 = true -> (i <= N)%nat ->
 no_trap (kont (iter i c0)) = true /\ not_throw (iter i c0) = true /\
 ((i < N)%nat -> is_tau (next_r R P (iter i c0)) = true) /\ (i = N -> is_final (next_r R P (iter i c0)) = true).
Proof.
 intros N c0 i H L. unfold chain_ok in H. apply andb_prop in H as [H Nt]. apply andb_prop in H as [H Ntr].
 apply andb_prop in H as [H Fin].
 destruct (Nat.eq_dec i N) as [->|Ne].
 - split; [exact Ntr|split; [exact Nt|split; [intros; lia|intros _; exact Fin]]].
 - assert (I : In i (seq 0 N)) by (apply in_seq; lia).
   pose proof (proj1 (forallb_forall _ _) H i I) as Hi. cbn beta in Hi.
   apply andb_prop in Hi as [Hi Nti]. apply andb_prop in Hi as [Ti Ntri].
   split; [exact Ntri|split; [exact Nti|split; [intros; exact Ti|intros; lia]]].
Qed.

Lemma resource_user : forall r x, resource_exn R r = Some x -> exists m, x = XUser m.
Proof. intros [] x E; cbn in E; injection E as <-; eexists; reflexivity. Qed.

Definition Inv (N : nat) (c0 c : config) : Prop :=
 (exists i, (i <= N)%nat /\ c = iter i c0) \/
 (exists x k s, c = Cfg (Throw x) k s /\ (exists m, x = XUser m) /\ no_trap k = true).

Lemma throw_no_trap : forall x f k s, no_trap (f :: k) = true -> next_r R P (Cfg (Throw x) (f :: k) s) = MTau (Cfg (Throw x) k s).
Proof. intros x f k s H. destruct f; cbn in H |- *; try reflexivity; discriminate. Qed.

Lemma Inv_step : forall N c0 c l c', chain_ok N c0 = true -> Inv N c0 c -> step_r R P c l c' -> Inv N c0 c'.
Proof.
 intros N c0 c l c' Ok [(i & L & ->)|(x & k & s & -> & Ux & Nk)] St.
 - destruct (chain_at N c0 i Ok L) as (Nt & Nth & Tau & Fin).
   inversion St as [c1 c2 E|c1 q kk r E|c1 r x Run Rx]; subst.
   + destruct (Nat.eq_dec i N) as [->|Ne].
     * specialize (Fin eq_refl). rewrite E in Fin. discriminate.
     * left. exists (S i). split; [lia|]. cbn [iter]. rewrite E. reflexivity.
   + destruct (Nat.eq_dec i N) as [->|Ne].
     * specialize (Fin eq_refl). rewrite E in Fin. discriminate.
     * assert (Lt : (i < N)%nat) by lia. specialize (Tau Lt). rewrite E in Tau. discriminate.
   + right. exists x, (kont (iter i c0)), (mem (iter i c0)). split; [reflexivity|].
     split; [eapply resource_user; exact Rx|exact Nt].
 - inversion St as [c1 c2 E|c1 q kk r E|c1 r y Run Ry]; subst.
   + destruct k as [|f k]; [cbn in E; discriminate|]. rewrite throw_no_trap in E by exact Nk.
     injection E as <-. right. exists x, k, s. split; [reflexivity|split; [exact Ux|]].
     cbn in Nk. apply andb_prop in Nk as [_ Nk]. exact Nk.
   + destruct k as [|f k]; [cbn in E; discriminate|]. rewrite throw_no_trap in E by exact Nk. discriminate.
   + cbn in Run. discriminate.
Qed.

(* No source run from a chain's start raises (XUnboundVar y) to the top. *)
Theorem no_reach_iter : forall N c0 t s y, chain_ok N c0 = true ->
 srun sealed c0 t (Cfg (Throw (XUnboundVar y)) [] s) -> False.
Proof.
 intros N c0 t s y Ok Run.
 assert (G : forall c t c', star (step_r R P) c t c' -> Inv N c0 c -> Inv N c0 c').
 { intros c t' c' St. induction St as [c|c l c1 t' c2 St1 St IH]; intros I; [exact I|].
   apply IH. eapply Inv_step; [exact Ok|exact I|exact St1]. }
 destruct (G _ _ _ Run (or_introl (ex_intro _ 0 (conj (Nat.le_0_l N) eq_refl))))
   as [(i & L & E)|(x & k & s' & E & (m & Ex) & _)].
 - destruct (chain_at N c0 i Ok L) as (_ & Nth & _). rewrite <- E in Nth. discriminate.
 - injection E as E1 _ _. rewrite Ex in E1. discriminate.
Qed.

(* Forward iteration, for the target's run. *)
Fixpoint tau_all (n : nat) (c : config) : bool := match n with
 | O => true
 | S n => match next_r R P c with MTau c' => tau_all n c' | _ => false end end.
Fixpoint iterf (n : nat) (c : config) : config := match n with
 | O => c
 | S n => match next_r R P c with MTau c' => iterf n c' | _ => c end end.

Lemma runs_iterf : forall n c, tau_all n c = true -> runs sealed n c [] (iterf n c).
Proof.
 induction n as [|n IH]; intros c H; [constructor|]. cbn [tau_all] in H. cbn [iterf].
 destruct (next_r R P c) eqn:E; try discriminate.
 change (@nil event) with (trace_of Tau ++ []). econstructor; [apply step_r_tau; exact E|]. apply IH. exact H.
Qed.
End Chain.

Section Cx.
(* KRef of (freeze id_key) against itself in the empty scope: inside the closure both sides read
   their own identity cell, which the world relates. *)
Definition xfz : expr := EFreeze (EVar id_key).

Lemma KRef_xfz : forall sealed D, KRef sealed D [] xfz xfz.
Proof.
 intros sealed D k w rho0 rho Ww HE. apply JitKRefCompatClo.JitKRefCompatClo.frz_core.
 intros j w' l0 l Lj W I.
 eapply (JitKRefCompatCtl.JitKRefCompatCtl.ERel_sval sealed D j w' _ _ _ _ (VVec l0) (VVec l));
  [reflexivity|reflexivity|].
 eapply JitKRefCompatClo.JitKRefCompatClo.VRel_vec. exact I.
Qed.

Lemma wf_nil : wf_world [].
Proof. split; constructor. Qed.

(* From a KRef link at index k in empty environments and a one-store start, the target's raise of
   (XUnboundVar y) after n < k steps gives a source run raising it. *)
Lemma KRef_throw : forall sealed D e0 e s n y, D_wf sealed D -> StoreHas D s -> store_ok s -> heap s = [] ->
 KRef sealed D [] e0 e -> tau_all sealed n (Cfg (Eval [] e) [] s) = true ->
 iterf sealed n (Cfg (Eval [] e) [] s) = Cfg (Throw (XUnboundVar y)) [] s ->
 exists t s0, srun sealed (Cfg (Eval [] e0) [] s) t (Cfg (Throw (XUnboundVar y)) [] s0).
Proof.
 intros sealed D e0 e s n y Dw SH SO Hp H Ta It.
 assert (Er := H (S n) [] [] [] wf_nil (fun x I => match I with end)).
 rewrite JitKRefBase.JitKRefBase.ERel_iff in Er.
 assert (HS := JitKRefFund.JitKRefFund.store_refl sealed D (S n) s Dw SH SO).
 assert (Ew : id_world s = []) by (unfold id_world; rewrite Hp; reflexivity). rewrite Ew in HS.
 assert (O := Er (S n) (le_n _) [] (conj (incl_refl _) wf_nil) [] []
   (JitKRefGround.JitKRefGround.KRel_top sealed D (S n) [] wf_nil) s s HS).
 destruct (O n [] (iterf sealed n (Cfg (Eval [] e) [] s)) ltac:(lia) (runs_iterf sealed n _ Ta)) as (_ & Ot & _).
 destruct (Ot (XUnboundVar y) s It) as (s0 & w' & Run & _). exists [], s0. exact Run.
Qed.

(* ---------- inline site ---------- *)
Definition f_cx : name := kw "f".
Definition p_cx : name := kw "p".
Definition sealed_cx : list name := [f_cx].
Definition D_cx : list (name * fundef) := [(f_cx, FUser [p_cx] (EApp (EVar p_cx) []))].
Definition s_cx : store := Store [] [] D_cx.

Lemma D_cx_wf : D_wf sealed_cx D_cx.
Proof. split; [repeat constructor|repeat constructor; intros []]. Qed.

Lemma s_cx_has : StoreHas D_cx s_cx.
Proof. intros f d [E|[]]. injection E as <- <-. reflexivity. Qed.

Lemma s_cx_ok : store_ok s_cx.
Proof. split; constructor. Qed.

(* The checker accepts the site: (f (freeze id_key)) expanded with the frozen argument thawed in
   place, which is the bare variable id_key. *)
Example inl_site_cx : F.inl_site false false D_cx f_cx [xfz] (EVar id_key) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_cx : chain_ok sealed_cx 7 (Cfg (Eval [] (ECall f_cx [xfz])) [] s_cx) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem inline_site_unsound : ~ F.inline_site_sound_statement sealed_cx D_cx.
Proof.
 intros H.
 assert (K := H false false [] f_cx [xfz] [xfz] (EVar id_key) D_cx_wf
   (fun E => ltac:(discriminate E)) (fun E => ltac:(discriminate E)) inl_site_cx
   (Forall2_cons _ _ (KRef_xfz sealed_cx D_cx) (Forall2_nil _))).
 destruct (KRef_throw sealed_cx D_cx _ _ s_cx 1 id_key D_cx_wf s_cx_has s_cx_ok eq_refl K
   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (t & s0 & Run).
 exact (no_reach_iter sealed_cx 7 _ t s0 id_key chain_cx Run).
Qed.

(* ---------- bound-now site ---------- *)
Definition q1 : name := kw "x1". Definition q2 : name := kw "x2".
Definition q3 : name := kw "x3". Definition q4 : name := kw "x4".
Definition a1 : name := kw "a1". Definition a2 : name := kw "a2". Definition a3 : name := kw "a3".
Definition d1 : name := kw "d1". Definition d2 : name := kw "d2".
Definition sealed_bx : list name := [F.bind_name; JitNorm.JitNorm.do_name].
Definition D_bx : list (name * fundef) :=
 [(F.bind_name, FUser [q1; q2; q3; q4] (EApp (EVar q4) []));
  (JitNorm.JitNorm.do_name, FUser [d1; d2] (EVar d2))].
Definition s_bx : store := Store [] [] D_bx.
Definition nargs_bx : list expr := [ENum (NInt 1); ENum (NInt 2); ENum (NInt 3); xfz].
Definition e_bx : expr := ELet a1 (ENum (NInt 1)) (ELet a2 (ENum (NInt 2)) (ELet a3 (ENum (NInt 3)) (EVar id_key))).

Lemma D_bx_wf : D_wf sealed_bx D_bx.
Proof.
 split.
 - constructor; [left; reflexivity|constructor; [right; left; reflexivity|constructor]].
 - constructor; [|constructor; [intros []|constructor]].
   intros [E|[]]. assert (B : text_eqb F.bind_name JitNorm.JitNorm.do_name = false) by (vm_compute; reflexivity).
   cbn [map fst] in E. rewrite E, text_eqb_refl in B. discriminate.
Qed.

Lemma s_bx_has : StoreHas D_bx s_bx.
Proof. intros f d [E|[E|[]]]; injection E as <- <-; vm_compute; reflexivity. Qed.

Lemma s_bx_ok : store_ok s_bx.
Proof. split; constructor. Qed.

Lemma D_bx_do : F.D_has_kernel_do D_bx.
Proof.
 exists d1, d2. split; [|right; left; reflexivity].
 intros E. assert (B : text_eqb d1 d2 = false) by (vm_compute; reflexivity). rewrite E, text_eqb_refl in B. discriminate.
Qed.

Example bind_site_cx : F.bind_site false D_bx nargs_bx e_bx = true.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_bx : chain_ok sealed_bx 13 (Cfg (Eval [] (ECall F.bind_name nargs_bx)) [] s_bx) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem bind_site_unsound : ~ F.bind_site_sound_statement sealed_bx D_bx.
Proof.
 intros H.
 assert (K := H false [] nargs_bx nargs_bx e_bx D_bx_wf (fun E => ltac:(discriminate E)) D_bx_do bind_site_cx
   (Forall2_cons _ _ (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed_bx D_bx [] (ENum (NInt 1)) (VNum (NInt 1)) eq_refl)
   (Forall2_cons _ _ (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed_bx D_bx [] (ENum (NInt 2)) (VNum (NInt 2)) eq_refl)
   (Forall2_cons _ _ (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed_bx D_bx [] (ENum (NInt 3)) (VNum (NInt 3)) eq_refl)
   (Forall2_cons _ _ (KRef_xfz sealed_bx D_bx) (Forall2_nil _)))))).
 destruct (KRef_throw sealed_bx D_bx _ _ s_bx 10 id_key D_bx_wf s_bx_has s_bx_ok eq_refl K
   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (t & s0 & Run).
 exact (no_reach_iter sealed_bx 13 _ t s0 id_key chain_bx Run).
Qed.
End Cx.

End JitFrontInline.
