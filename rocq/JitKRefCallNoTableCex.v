(* Shen/JIT Phase 2: call_rel needs SRel's function-table equality (r21-mutation-hygiene).
   JitKRefCompatClo.call_rel relates two named-call moves, call_named_r g on both sides, from
   related arguments, continuations and stores. Its proof rewrites with gfuns s0 = gfuns s, the
   table clause of SRel_with, so both sides look g up in one table.

   Mutant ShenJitKRefCallNoTable (tests/mutate-shen-jit.py) drops that clause from SRel_with and
   GStore, and Rocq rejects call_rel's proof. That rejection alone shows the proof stops, not
   that the statement is false. This file shows the statement false in Rocq:
   - SRel_nt is SRel_with's text with the table clause replaced by True (the mutant's edit), over
     the unmutated VRel;
   - call_rel_nt_statement is call_rel's statement with SRel replaced by SRel_nt, and nothing else
     changed;
   - call_rel_nt_of_table: with gfuns s0 = gfuns s added back, call_rel_nt_statement's
     conclusion follows from call_rel, so the table clause is the only difference;
   - call_rel_no_table_refuted: ~ call_rel_nt_statement [] []. Every premise holds: fund_below 3
     from JitKRefFund.fund_gen, prim_compat_statement from JitKRefPrim.prim_compat, KRel_top,
     AppAll from JitKRefCompatClo.app_at, and SRel_nt for two stores that differ only in their
     tables. The source table lacks g, so the source call raises (XUndefinedFun g). The target
     table defines g as (defun g () 1), so the target returns 1 in one step. ObsT 2 requires a
     source run to a value, and the source's only reachable states are that exception. The
     two outcomes differ in kind (a value against an exception), so no GVal choice can relate
     them. cx_tables_differ proves the two tables differ, so SRel (with the clause) does not hold
   for these stores.

   Does NOT show: that the mutant's whole chain is false. The mutant also drops the clause from
   GStore, and its VRel, KRel, ERel and fund_below are built over its own SRel; here they are the
   unmutated ones. Under the mutant's definitions we expect fund_below (S j) itself to fail once j
   is large enough for ECall g [] to finish (the same two stores separate it from itself), so the
   mutant's own call_rel may hold vacuously there; that expectation is an informal argument, not
   checked here. The mutant therefore stays a rejected proof, and this file is the separate Rocq
   evidence that the table clause carries call_rel. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitKRefFv JitKRefFund JitLowerStage0 JitNorm JitNormStage0 JitFrontD JitFrontProlog.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefCallNoTableCex.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitKRef.JitKRef.

Section NoTable.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation KRel := (JitKRef.JitKRef.KRel sealed D).
Notation StoreHas := (JitKRef.JitKRef.StoreHas D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).
Notation prim_compat_statement := (JitKRef.JitKRef.prim_compat_statement sealed D).
Notation AppAll := (JitKRefBase.JitKRefBase.AppAll sealed D).
Notation MoveRel := (JitKRefCompatClo.JitKRefCompatClo.MoveRel sealed).

(* SRel_with (VRel k) with its table clause gfuns s0 = gfuns s replaced by True. *)
Definition SRel_nt (k : nat) (w : world) (s0 s : store) : Prop :=
 wf_world w /\ StoreHas s0 /\ StoreHas s /\ True /\
 Forall2 (fun p0 p => fst p0 = fst p /\ VRel k w (snd p0) (snd p)) (gvals s0) (gvals s) /\
 (forall l0 l, In (l0, l) w -> exists c0 c, nth_error (heap s0) l0 = Some c0 /\
    nth_error (heap s) l = Some c /\ Forall2 (VRel k w) c0 c).

(* call_rel's statement, with SRel_nt for SRel. *)
Definition call_rel_nt_statement : Prop := forall j w g vs0 vs K0 K s0 s,
 fund_below (S j) -> prim_compat_statement ->
 KRel j w K0 K -> AppAll j w K0 K -> Forall2 (VRel j w) vs0 vs -> SRel_nt j w s0 s ->
 MoveRel j w (call_named_r R P g vs0 K0 s0) (call_named_r R P g vs K s).

(* SRel is SRel_nt plus the table clause. *)
Lemma SRel_nt_table : forall k w s0 s, SRel k w s0 s <-> SRel_nt k w s0 s /\ gfuns s0 = gfuns s.
Proof.
 intros k w s0 s. split.
 - intros (W & H0 & H1 & G & Fv & Hh). exact (conj (conj W (conj H0 (conj H1 (conj I (conj Fv Hh))))) G).
 - intros [(W & H0 & H1 & _ & Fv & Hh) G]. exact (conj W (conj H0 (conj H1 (conj G (conj Fv Hh))))).
Qed.

(* With the table clause added back, call_rel gives the conclusion. *)
Theorem call_rel_nt_of_table : forall j w g vs0 vs K0 K s0 s,
 fund_below (S j) -> prim_compat_statement ->
 KRel j w K0 K -> AppAll j w K0 K -> Forall2 (VRel j w) vs0 vs -> SRel_nt j w s0 s -> gfuns s0 = gfuns s ->
 MoveRel j w (call_named_r R P g vs0 K0 s0) (call_named_r R P g vs K s).
Proof.
 intros j w g vs0 vs K0 K s0 s F PC HK HA Hv HS G.
 exact (JitKRefCompatClo.JitKRefCompatClo.call_rel sealed D j w g vs0 vs K0 K s0 s F PC HK HA Hv
   (proj2 (SRel_nt_table j w s0 s) (conj HS G))).
Qed.
End NoTable.

(* ======================= the counterexample ======================= *)
Definition cx_g : name := of_string "f".
Definition cx_s0 : store := Store [] [] [].
Definition cx_s : store := Store [] [] [(cx_g, FUser [] (ENum (NInt 1)))].
Definition cx_c0 : config := Cfg (Throw (XUndefinedFun cx_g)) [] cx_s0.
Definition cx_c : config := Cfg (Eval [] (ENum (NInt 1))) [] cx_s.

Example cx_src_move : call_named_r (jit_rules []) jit_profile cx_g [] [] cx_s0 = MTau cx_c0.
Proof. vm_compute. reflexivity. Qed.

Example cx_tgt_move : call_named_r (jit_rules []) jit_profile cx_g [] [] cx_s = MTau cx_c.
Proof. vm_compute. reflexivity. Qed.

(* The two tables differ, so SRel's table clause is false for this pair of stores: with the clause
   restored, no proof of SRel_nt for them exists (mutant ShenJitKRefCallNoTableCexTable). *)
Lemma cx_tables_differ : gfuns cx_s0 <> gfuns cx_s.
Proof. intros E. vm_compute in E. discriminate E. Qed.

Theorem call_rel_no_table_refuted : ~ call_rel_nt_statement [] [].
Proof.
 intros H.
 assert (Dw : JitKRef.JitKRef.D_wf [] []) by (split; constructor).
 assert (Wf : wf_world []) by (split; constructor).
 pose proof (JitKRefFund.JitKRefFund.fund_gen [] [] Dw 2) as Fb.
 pose proof (JitKRefPrim.JitKRefPrim.prim_compat [] []) as PC.
 pose proof (JitKRefGround.JitKRefGround.KRel_top [] [] 2 [] Wf) as HK.
 assert (HA : JitKRefBase.JitKRefBase.AppAll [] [] 2 [] [] []).
 { apply (JitKRefCompatClo.JitKRefCompatClo.AppAll_of_AppAt [] []); [|exact HK].
   intros i L. apply (JitKRefCompatClo.JitKRefCompatClo.app_at [] [] 3 Fb PC i). lia. }
 assert (HS : SRel_nt [] [] 2 [] cx_s0 cx_s).
 { split; [exact Wf|split; [intros f d []|split; [intros f d []|split; [exact I|split; [constructor|intros l0 l []]]]]]. }
 specialize (H 2 [] cx_g [] [] [] [] cx_s0 cx_s Fb PC HK HA (Forall2_nil _) HS).
 rewrite cx_src_move, cx_tgt_move in H. cbn [JitKRefCompatClo.JitKRefCompatClo.MoveRel] in H.
 assert (Ht : JitKRef.JitKRef.runs [] 1 cx_c [] (Cfg (Ret (VNum (NInt 1))) [] cx_s)).
 { apply JitFrontProlog.JitFrontProlog.iter_runs. vm_compute. reflexivity. }
 destruct (H 1%nat [] _ ltac:(lia) Ht) as [Hret _].
 destruct (Hret (VNum (NInt 1)) cx_s eq_refl) as (v0 & s0 & w' & Hs & _).
 assert (HC : forall i c, (i <= 0)%nat -> JitFrontProlog.JitFrontProlog.iter_tau [] i cx_c0 = Some c ->
   JitFrontProlog.JitFrontProlog.no_io (next_r (jit_rules []) jit_profile c) = true /\
   forallb JitKRefBase.JitKRefBase.nontrap (kont c) = true).
 { intros i c L Ei. assert (i = 0%nat) by lia. subst i. cbn in Ei. injection Ei as <-.
   split; vm_compute; reflexivity. }
 assert (HN : JitFrontProlog.JitFrontProlog.iter_tau [] 1 cx_c0 = None) by (vm_compute; reflexivity).
 destruct (JitFrontProlog.JitFrontProlog.star_reach [] cx_c0 0 HC HN [] _ Hs) as [(i & L & Ei)|(x & K & s & E & _)].
 - assert (i = 0%nat) by lia. subst i. cbn in Ei. discriminate Ei.
 - discriminate E.
Qed.
End JitKRefCallNoTableCex.
