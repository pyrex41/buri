(* Shen/JIT Phase 2: KRef's compatibility lemma for a named call (r1-compat-call).
   The statement compat_call_statement is JitKTerm.v's; this file re-opens Section Equiv with
   JitKTerm.v's Variables and proves:

   - ERel_call_nil: (ECall f []) against itself at index k. Both sides' first move is
     call_named_r f [] through the function table; JitKTermCompatClo.call_rel relates the two moves
     one index down (SRel makes the two tables equal; a user body by fund_below, a primitive by
     prim_compat_statement, an unbound name raising XUndefinedFun, an arity error raising alike, a
     short call returning related partial applications) and JitKTermCompatCtl.ObsT_of_MRel pays the
     target's step.
   - ERel_call_cons: (ECall f (a0 :: rest0)) against (ECall f (a :: rest)). Both sides push
     KCallArgs f [] rest rho; JitKTermBase.KRel_KCallArgs relates the frames, given AppRel of
     (VPartial f []) against itself, which JitKTermCompatClo.app_rel gives (AppAll at index j from
     fund_below j and prim_compat_statement, applied to VRel_partial_j of no arguments).
   - compat_call_core: the two together, for arguments related at every j < k.
   - compat_call_lt_pc, compat_call_lt: compat_call at index k (KRef-related arguments, scope g)
     from fund_below k; the first takes prim_compat_statement, the second discharges it with
     JitKTermPrim.prim_compat.
   - compat_call_refl_lt: the reflexive form JitKTermFund's induction uses, in fund_below's scope
     form (FvOk), from fund_below k alone.
   - compat_call_of_fund: compat_call_statement from fund_gen_statement alone. D_wf is the
     statement's own premise, and is what fund_gen_statement takes.

   The callee's identity is the same on both sides (the statement relates ECall f to ECall f); the
   callee's definition is the same because SRel's gfuns clause makes the two function tables equal
   at every store the relation reaches, so neither sealed_stable nor storehas_stable is needed
   here directly: SRel carries StoreHas and the table equality, and every step that changes a
   table (defun) is the business of the frames that return through KRel.
   Mutant ShenJitKTermCallNoTable drops that table equality from SRel (and GStore); Rocq then
   rejects JitKTermCompatClo.call_rel, the call move this file uses.

   NOT proved here: fund_gen_statement, the fundamental property (JitKTermFund). *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKTerm JitKTermGround JitKTermBase JitKTermCompatClo JitKTermPrim JitKTermCompatCtl.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKTermCompatCall.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKTerm.JitKTerm
 JitKTermGround.JitKTermGround JitKTermBase.JitKTermBase.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Notation ObsT := (JitKTerm.JitKTerm.ObsT sealed).
Notation VRel := (JitKTerm.JitKTerm.VRel sealed D).
Notation SRel := (JitKTerm.JitKTerm.SRel sealed D).
Notation KRel := (JitKTerm.JitKTerm.KRel sealed D).
Notation ERel := (JitKTerm.JitKTerm.ERel sealed D).
Notation KRef := (JitKTerm.JitKTerm.KRef sealed D).
Notation D_wf := (JitKTerm.JitKTerm.D_wf sealed D).
Notation fund_below := (JitKTerm.JitKTerm.fund_below sealed D).
Notation fund_gen_statement := (JitKTerm.JitKTerm.fund_gen_statement sealed D).
Notation prim_compat_statement := (JitKTerm.JitKTerm.prim_compat_statement sealed D).
Notation compat_call_statement := (JitKTerm.JitKTerm.compat_call_statement sealed D).
Notation ERel_iff := (JitKTermBase.JitKTermBase.ERel_iff sealed D).
Notation ERel_push := (JitKTermBase.JitKTermBase.ERel_push sealed D).
Notation KRel_down := (JitKTermBase.JitKTermBase.KRel_down sealed D).
Notation SRel_down := (JitKTermBase.JitKTermBase.SRel_down sealed D).
Notation KRel_throw := (JitKTermBase.JitKTermBase.KRel_throw sealed D).
Notation KRel_KCallArgs := (JitKTermBase.JitKTermBase.KRel_KCallArgs sealed D).
Notation EnvRel_mono := (JitKTermBase.JitKTermBase.EnvRel_mono sealed D).
Notation ObsT_0 := (JitKTermBase.JitKTermBase.ObsT_0 sealed).
Notation MoveRel := (JitKTermCompatClo.JitKTermCompatClo.MoveRel sealed).
Notation call_rel := (JitKTermCompatClo.JitKTermCompatClo.call_rel sealed D).
Notation app_rel := (JitKTermCompatClo.JitKTermCompatClo.app_rel sealed D).
Notation VRel_partial_j := (JitKTermCompatClo.JitKTermCompatClo.VRel_partial_j sealed D).
Notation FvOk := JitKTermCompatClo.JitKTermCompatClo.FvOk.
Notation MRel := (JitKTermCompatCtl.JitKTermCompatCtl.MRel sealed).
Notation ObsT_of_MRel := (JitKTermCompatCtl.JitKTermCompatCtl.ObsT_of_MRel sealed).

Lemma fund_below_down : forall k j, (j <= k)%nat -> fund_below k -> fund_below j.
Proof. intros k j L F i Li. apply F. lia. Qed.

(* CompatClo's MoveRel and CompatCtl's MRel are the same relation on moves. *)
Lemma MoveRel_MRel : forall j w m0 m, MoveRel j w m0 m -> MRel j w m0 m.
Proof. intros j w m0 m H. destruct m0, m; exact H. Qed.

Lemma next_call_nil : forall rho f K s,
 next_r R P (Cfg (Eval rho (ECall f [])) K s) = call_named_r R P f [] K s.
Proof. reflexivity. Qed.

(* AppRel of the partial application of f to no arguments, against itself: what KRel_KCallArgs
   needs for the call that ends the argument list. *)
Lemma AppRel_partial_nil : forall j w f K0 K, fund_below j -> prim_compat_statement -> wf_world w ->
 KRel j w K0 K -> JitKTermBase.JitKTermBase.AppRel sealed D j w (VPartial f []) (VPartial f []) K0 K.
Proof.
 intros j w f K0 K F PC Wf HK. apply (app_rel j w K0 K F PC HK j w); [apply le_n|apply wext_refl; exact Wf|].
 apply VRel_partial_j. constructor.
Qed.

(* ======================= a call with no arguments ======================= *)
Theorem ERel_call_nil : forall k w rho0 rho f, fund_below k -> prim_compat_statement ->
 ERel k w rho0 (ECall f []) rho (ECall f []).
Proof.
 intros k w rho0 rho f F PC. apply ERel_iff. intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply ObsT_0|].
 assert (HK' : KRel j w' K0 K) by (eapply KRel_down; [|exact HK]; lia).
 assert (HS' : SRel j w' s0 s) by (eapply SRel_down; [|exact HS]; lia).
 apply ObsT_of_MRel; [reflexivity| |].
 - intros x. cbn [kont mem]. apply KRel_throw; assumption.
 - rewrite !next_call_nil. apply MoveRel_MRel.
   apply call_rel; [eapply fund_below_down; [|exact F]; lia|exact PC|exact HK'| |constructor|exact HS'].
   apply app_rel; [eapply fund_below_down; [|exact F]; lia|exact PC|exact HK'].
Qed.

(* ======================= a call with arguments ======================= *)
Theorem ERel_call_cons : forall k w rho0 rho f a0 rest0 a rest, fund_below k -> prim_compat_statement ->
 (forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 a0 rho a) ->
 Forall2 (fun a0 a => forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 a0 rho a) rest0 rest ->
 ERel k w rho0 (ECall f (a0 :: rest0)) rho (ECall f (a :: rest)).
Proof.
 intros k w rho0 rho f a0 rest0 a rest F PC Ha Hrest.
 apply (ERel_push k w rho0 (ECall f (a0 :: rest0)) rho (ECall f (a :: rest)) rho0 a0 rho a
   (fun K0 => KCallArgs f [] rest0 rho0 :: K0) (fun K => KCallArgs f [] rest rho :: K)).
 - intros K0 s0. reflexivity.
 - intros K s. reflexivity.
 - intros j w' K0 K Lj W HK. apply KRel_KCallArgs; [exact HK| |constructor|].
   + apply AppRel_partial_nil; [eapply fund_below_down; [|exact F]; lia|exact PC|apply W|exact HK].
   + eapply Forall2_impl; [|exact Hrest]. intros b0 b Hb. apply Hb; assumption.
 - exact Ha.
Qed.

(* A named call from its arguments related below k. *)
Theorem compat_call_core : forall k w rho0 f as0 rho as1, fund_below k -> prim_compat_statement ->
 Forall2 (fun a0 a => forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 a0 rho a) as0 as1 ->
 ERel k w rho0 (ECall f as0) rho (ECall f as1).
Proof.
 intros k w rho0 f as0 rho as1 F PC Has. destruct Has as [|a0 a rest0 rest Ha Hrest].
 - apply ERel_call_nil; assumption.
 - apply ERel_call_cons; assumption.
Qed.

(* compat_call at index k, from fund_below k and prim_compat_statement. *)
Theorem compat_call_lt_pc : prim_compat_statement -> forall k, fund_below k ->
 forall g f as0 as1, Forall2 (KRef g) as0 as1 ->
 forall w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 (ECall f as0) rho (ECall f as1).
Proof.
 intros PC k F g f as0 as1 Has w rho0 rho Wf HE. apply compat_call_core; [exact F|exact PC|].
 eapply Forall2_impl; [|exact Has]. intros a0 a Ha j w' Lj W.
 apply Ha; [apply W|eapply EnvRel_mono; [|exact W|exact HE]; lia].
Qed.

(* compat_call at index k from fund_below k alone: JitKTermPrim proves prim_compat_statement. *)
Theorem compat_call_lt : forall k, fund_below k ->
 forall g f as0 as1, Forall2 (KRef g) as0 as1 ->
 forall w rho0 rho, wf_world w -> EnvRel_with (VRel k) w g rho0 rho -> ERel k w rho0 (ECall f as0) rho (ECall f as1).
Proof. exact (compat_call_lt_pc (JitKTermPrim.JitKTermPrim.prim_compat sealed D)). Qed.

Lemma FvOk_call_args : forall g rho0 rho f args, FvOk g rho0 rho (ECall f args) -> Forall (FvOk g rho0 rho) args.
Proof.
 intros g rho0 rho f args. induction args as [|a rest IH]; intros H; constructor.
 - intros y I. apply H. cbn [fv]. apply in_or_app. left. exact I.
 - apply IH. intros y I. apply H. cbn [fv] in *. apply in_or_app. right. exact I.
Qed.

(* The reflexive form JitKTermFund's induction uses, in fund_below's scope form. *)
Theorem compat_call_refl_lt : forall k w g rho0 rho f args, fund_below k -> wf_world w ->
 EnvRel_with (VRel k) w g rho0 rho -> FvOk g rho0 rho (ECall f args) ->
 ERel k w rho0 (ECall f args) rho (ECall f args).
Proof.
 intros k w g rho0 rho f args F Wf HE Hfv.
 apply compat_call_core; [exact F|exact (JitKTermPrim.JitKTermPrim.prim_compat sealed D)|].
 pose proof (FvOk_call_args g rho0 rho f args Hfv) as Fa. clear Hfv.
 induction Fa as [|a rest Ha Fa IH]; constructor; [|exact IH].
 intros j w' Lj W. apply (F j Lj w' g); [apply W|eapply EnvRel_mono; [|exact W|exact HE]; lia|exact Ha].
Qed.

(* compat_call_statement from fund_gen_statement alone (kref-fund owns fund_gen_statement). *)
Theorem compat_call_of_fund : fund_gen_statement -> compat_call_statement.
Proof.
 intros FG g f as0 as1 Dw Has k w rho0 rho Wf HE.
 assert (F : fund_below k) by (apply (fund_below_down (S k)); [lia|apply FG; exact Dw]).
 exact (compat_call_lt k F g f as0 as1 Has w rho0 rho Wf HE).
Qed.
End Equiv.
End JitKTermCompatCall.
