(* Shen/JIT Phase 2: preservation over many steps, and its statement for a function call.
   For code the relation in JitLowerRel.v accepts, a run of the bytecode either keeps a related
   source configuration after any number of its steps, or ends as the source does: a related
   value, or an error both raise. The source may also raise a catchable stack or heap error
   wherever the bytecode does (KLPort.step_r_resource, a broad permission: OB-JIT-RESOURCES).
   This is about accepted code. Whether lower.shen's output is accepted is checked per definition
   (JitLowerCheck.v), and proving it for every input is OB-JIT-LOWER-GENERAL. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia Wf_nat.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitMeta JitProfile JitLowerRel JitLowerKont JitLowerStable JitLowerPrim JitLowerStep.
Import ListNotations.
Module JitLowerThm.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerStable.JitLowerStable JitLowerPrim.JitLowerPrim JitLowerStep.JitLowerStep.
Local Open Scope N_scope.
Module B := JitBytecode.JitBytecode.

Section Thm.
Variables (E : B.env) (pt : B.tree (B.prim * nat)) (sealed : list name).

(* Exactly n bytecode steps. *)
Inductive TN : nat -> B.machine -> B.machine -> Prop :=
 | TN_0 m : TN 0 m m
 | TN_S n m m1 m2 : TS E pt m m1 -> TN n m1 m2 -> TN (S n) m m2.

Inductive Ends (s : store) (c : config) : Prop :=
 | E_ok v v' m1 m2 : Sstar sealed c (Cfg (Ret v) [] s) -> B.next E pt m1 = B.MFinal (B.FReturn v') m2 -> VR v v' -> Ends s c
 | E_err x l msg tv m1 m2 : Sstar sealed c (Cfg (Throw x) [] s) -> B.next E pt m1 = B.MFinal (B.FError (B.VExn l)) m2 ->
     B.tget l (B.m_heap m2) = Some (B.OExn msg tv) -> exn_ok x msg -> Ends s c.

Lemma TStar_TN : forall a b, TStar E pt a b -> exists n, TN n a b.
Proof. intros a b H; induction H; [exists 0%nat; constructor|destruct IHTStar as [n T]; exists (S n); econstructor; eauto]. Qed.

(* After n steps of the bytecode: still related, or the run has ended as the source's does. *)
Theorem preservation : forall n s c m, MS s c m ->
 (exists c' m' k, Sstar sealed c c' /\ TN k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, Ends s c /\ TStar E pt m m1).
Proof.
 induction n as [|n IHn]; intros s c m H.
 - left. exists c, m, 0%nat. repeat split; [constructor|constructor|lia|exact H].
 - revert m H. induction c as [c IHc] using (well_founded_induction (well_founded_ltof _ msr)).
   intros m H. destruct (sim E pt sealed s c m H) as [c' m' Ss [[m1 [T1 Ts]]|[-> L]] M|v v' m1 m2 Ss Ts Nf Vr|x l msg tv m1 m2 Ss Ts Nf Lh Xo].
   + destruct (IHn s c' m' M) as [(c2 & m2 & k & S2 & T2 & L2 & M2)|(m2 & En & T2)].
     * destruct (TStar_TN _ _ Ts) as [j Tj].
       left. exists c2, m2, (S (j + k)). repeat split.
       -- eapply Sstar_trans; eauto.
       -- econstructor; [exact T1|]. clear -Tj T2. induction Tj; [exact T2|econstructor; eauto].
       -- lia.
       -- exact M2.
     * right. exists m2. split.
       -- inversion En; subst; [eapply E_ok|eapply E_err]; try (eapply Sstar_trans; [exact Ss|eassumption]); eassumption.
       -- econstructor; [exact T1|]. eapply TStar_trans; eauto.
   + destruct (IHc c' L m M) as [(c2 & m2 & k & S2 & T2 & L2 & M2)|(m2 & En & T2)].
     * left. exists c2, m2, k. repeat split; [eapply Sstar_trans; eauto|exact T2|exact L2|exact M2].
     * right. exists m2. split; [|exact T2].
       inversion En; subst; [eapply E_ok|eapply E_err]; try (eapply Sstar_trans; [exact Ss|eassumption]); eassumption.
   + right. exists m1. split; [eapply E_ok; eauto|exact Ts].
   + right. exists m1. split; [eapply E_err; eauto|exact Ts].
Qed.

(* A step the bytecode can take is matched: no related state is stuck, and none takes IO. *)
Corollary related_progress : forall s c m, MS s c m ->
 (exists m', TPlus E pt m m') \/ (exists m1, Ends s c /\ TStar E pt m m1) \/
 (exists c', Sstar sealed c c' /\ (msr c' < msr c)%nat /\ MS s c' m).
Proof.
 intros s c m H. destruct (sim E pt sealed s c m H) as [c' m' Ss [Tp|[-> L]] M|v v' m1 m2 Ss Ts Nf Vr|x l msg tv m1 m2 Ss Ts Nf Lh Xo].
 - left; eauto.
 - right; right; eauto.
 - right; left. exists m1. split; [eapply E_ok; eauto|exact Ts].
 - right; left. exists m1. split; [eapply E_err; eauto|exact Ts].
Qed.

(* ---------- a call from the top level ---------- *)
(* The bytecode machine entering code c with these values in slots 2 up, nothing pending. *)
Definition entered (m : B.machine) (c : B.code) (args : list value) : Prop :=
 B.m_code m = c /\ B.m_rest m = B.code_ins c /\ B.m_conts m = [] /\
 ArgsAt (B.m_stack m) (B.m_fp m + 2) args.

Theorem call_preservation : forall s m c ps b args n,
 Com s m -> CompFn c ps b -> List.length ps = List.length args -> entered m c args ->
 let c0 := Cfg (Eval (combine ps args) b) [] s in
 (exists c' m' k, Sstar sealed c0 c' /\ TN k m m' /\ (n <= k)%nat /\ MS s c' m') \/
 (exists m1, Ends s c0 /\ TStar E pt m m1).
Proof.
 intros s m c ps b args n Cm [r' Cf] L [Hc [Hr [Hk Aa]]] c0.
 apply preservation. subst c0.
 eapply MS_eval with (g := bind ps 2) (top := 2 + N.of_nat (List.length ps)) (dst := DRet) (r2 := r')
   (w := fun a => B.m_fp m + (2 + N.of_nat (List.length ps)) <= a).
 - exact Cm.
 - rewrite Hc, Hr. exact Cf.
 - apply MEnv_bind; [exact L|exact Aa].
 - apply bind_below.
 - intros a A; exact A.
 - rewrite Hk. apply KC_ret; [intros a A; lia|constructor].
Qed.
End Thm.
End JitLowerThm.
