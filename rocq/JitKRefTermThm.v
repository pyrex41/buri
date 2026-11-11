(* Shen/JIT Phase 2: KTerm's theorems (OB-JIT-LOWER-TERM), in KTerm's orientation.
   KTerm sealed D g e0 e := JitKTerm.KRef sealed D g e e0 (rocq/JitKRefTerm.v). Everything here
   is proved from the JitKTerm* files, which are KRef's proof files over the resource-free rules,
   with no hypothesis beyond each statement's own:
   - the fundamental property (KTerm_refl, KTerm_fundamental) and every compatibility lemma
     (the KTerm_compat_ lemmas), each JitKTermFund / JitKTermCompatCtl / JitKTermCompatClo theorem read
     with the two expressions swapped;
   - per-link adequacy (KTerm_adequacy): a resource-free source run to a first-order value or an
     exception, from the same first-order environment and a well-formed store meeting D, is
     matched by a resource-free target run to the same value or exception; its contrapositive
     KTerm_diverges; and the two-link composition KTerm_compose (JitKRefTerm.KTerm_compose_statement),
     through the closed first-order observation and GStore_trans, without transitivity of KTerm;
   - per-rewrite lemmas. A front rule is checked for KRef as SOURCE ANTI-REDUCTION to an
     intermediate source term (JitKTermBase.ERel_anti_*: the existential side steps for free).
     For KTerm the source is the side whose runs are quantified, so the same rule is a SOURCE
     REDUCTION (ERel_red_*: the universal side's deterministic silent steps are free too, because
     under the resource-free rules every run of the source passes through its reduct). ERel_red is
     the general form; ERel_red_let, _if, _cond, _type, _call (a sealed callee inlined: the source
     calls it, the target has its body) and _app_lam are the KRef anti-reductions' counterparts,
     and KTerm_lambda_app is norm's ((lambda X B) A) to (let X A B) for an atomic A, as a
     compatibility-style rule with no transitivity. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKTerm JitKTermGround JitKTermBase JitKTermPrim JitKTermCompatCtl JitKTermCompatClo JitKTermCompatCall JitKTermFv JitKTermFund JitKRefTerm.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitKRefTermThm.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKTerm.JitKTerm JitKRefTerm.JitKRefTerm.

Section Term.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules_nr sealed).
Notation P := jit_profile.
Notation srun := (JitKTerm.JitKTerm.srun sealed).
Notation runs := (JitKTerm.JitKTerm.runs sealed).
Notation ObsT := (JitKTerm.JitKTerm.ObsT sealed).
Notation VRel := (JitKTerm.JitKTerm.VRel sealed D).
Notation SRel := (JitKTerm.JitKTerm.SRel sealed D).
Notation KRel := (JitKTerm.JitKTerm.KRel sealed D).
Notation ERel := (JitKTerm.JitKTerm.ERel sealed D).
Notation KRef := (JitKTerm.JitKTerm.KRef sealed D).
Notation KTerm := (JitKRefTerm.JitKRefTerm.KTerm sealed D).
Notation D_wf := (JitKTerm.JitKTerm.D_wf sealed D).
Notation StoreHas := (JitKTerm.JitKTerm.StoreHas D).
Notation EnvRelAll := (JitKTerm.JitKTerm.EnvRelAll sealed D).
Notation sval := JitKTermBase.JitKTermBase.sval.

(* ======================= the fundamental property and compatibility ======================= *)
Theorem KTerm_refl : forall g e, D_wf -> scoped g e = true -> KTerm g e e.
Proof. intros g e Dw S. exact (JitKTermFund.JitKTermFund.KRef_refl sealed D g e Dw S). Qed.

(* EnvRelAll in KTerm's orientation: the target's environment first. *)
Theorem KTerm_fundamental : forall k w rho rho0 e, D_wf -> wf_world w -> EnvRelAll k w rho rho0 ->
 ERel k w rho e rho0 e.
Proof. intros k w rho rho0 e Dw Ww H. exact (JitKTermFund.JitKTermFund.fundamental sealed D k w rho rho0 e Dw Ww H). Qed.

Lemma Forall2_flip : forall {A B} (Q : A -> B -> Prop) l1 l2,
 Forall2 Q l1 l2 -> Forall2 (fun b a => Q a b) l2 l1.
Proof. intros A B Q l1 l2 H. induction H; constructor; assumption. Qed.

Theorem KTerm_compat_lit : forall g e v, lit_val e = Some v -> KTerm g e e.
Proof. intros g e v H. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_lit sealed D g e v H). Qed.
Theorem KTerm_compat_var : forall g x, In x g -> KTerm g (EVar x) (EVar x).
Proof. intros g x H. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_var sealed D g x H). Qed.
Theorem KTerm_compat_let : forall g x a0 a b0 b,
 KTerm g a0 a -> KTerm (x :: g) b0 b -> KTerm g (ELet x a0 b0) (ELet x a b).
Proof. intros g x a0 a b0 b Ha Hb. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_let sealed D g x a a0 b b0 Ha Hb). Qed.
Theorem KTerm_compat_if : forall g c0 c a0 a b0 b,
 KTerm g c0 c -> KTerm g a0 a -> KTerm g b0 b -> KTerm g (EIf c0 a0 b0) (EIf c a b).
Proof. intros g c0 c a0 a b0 b Hc Ha Hb. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_if sealed D g c c0 a a0 b b0 Hc Ha Hb). Qed.
Theorem KTerm_compat_and : forall g a0 a b0 b, KTerm g a0 a -> KTerm g b0 b -> KTerm g (EAnd a0 b0) (EAnd a b).
Proof. intros g a0 a b0 b Ha Hb. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_and sealed D g a a0 b b0 Ha Hb). Qed.
Theorem KTerm_compat_or : forall g a0 a b0 b, KTerm g a0 a -> KTerm g b0 b -> KTerm g (EOr a0 b0) (EOr a b).
Proof. intros g a0 a b0 b Ha Hb. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_or sealed D g a a0 b b0 Ha Hb). Qed.
Theorem KTerm_compat_cond : forall g cl0 cl,
 Forall2 (fun p0 p => KTerm g (fst p0) (fst p) /\ KTerm g (snd p0) (snd p)) cl0 cl ->
 KTerm g (ECond cl0) (ECond cl).
Proof.
 intros g cl0 cl H. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_cond sealed D g cl cl0 (Forall2_flip _ _ _ H)).
Qed.
Theorem KTerm_compat_type : forall g a0 a, KTerm g a0 a -> KTerm g (EType a0) (EType a).
Proof. intros g a0 a H. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_type sealed D g a a0 H). Qed.
Theorem KTerm_compat_trap : forall g a0 a h0 h, D_wf -> KTerm g a0 a -> KTerm g h0 h -> KTerm g (ETrap a0 h0) (ETrap a h).
Proof. intros g a0 a h0 h Dw Ha Hh. exact (JitKTermFund.JitKTermFund.compat_trap sealed D g a a0 h h0 Dw Ha Hh). Qed.
Theorem KTerm_compat_lambda : forall g x b0 b, KTerm (x :: g) b0 b -> KTerm g (ELam x b0) (ELam x b).
Proof. intros g x b0 b H. exact (JitKTermCompatClo.JitKTermCompatClo.compat_lambda sealed D g x b b0 H). Qed.
Theorem KTerm_compat_freeze : forall g b0 b, KTerm g b0 b -> KTerm g (EFreeze b0) (EFreeze b).
Proof. intros g b0 b H. exact (JitKTermCompatClo.JitKTermCompatClo.compat_freeze sealed D g b b0 H). Qed.
Theorem KTerm_compat_call : forall g f as0 as1, D_wf -> Forall2 (KTerm g) as0 as1 -> KTerm g (ECall f as0) (ECall f as1).
Proof.
 intros g f as0 as1 Dw H. exact (JitKTermFund.JitKTermFund.compat_call sealed D g f as1 as0 Dw (Forall2_flip _ _ _ H)).
Qed.
Theorem KTerm_compat_app : forall g h0 h as0 as1, D_wf -> KTerm g h0 h -> Forall2 (KTerm g) as0 as1 ->
 KTerm g (EApp h0 as0) (EApp h as1).
Proof.
 intros g h0 h as0 as1 Dw Hh H.
 exact (JitKTermFund.JitKTermFund.compat_app sealed D g h h0 as1 as0 Dw Hh (Forall2_flip _ _ _ H)).
Qed.
Theorem KTerm_compat_defun : forall g f ps b, D_wf -> KTerm g (EDefun f ps b) (EDefun f ps b).
Proof. intros g f ps b Dw. exact (JitKTermCompatCtl.JitKTermCompatCtl.compat_defun sealed D g f ps b Dw). Qed.

(* ======================= adequacy, divergence, composition ======================= *)
(* One link: a resource-free source run from a first-order environment and a well-formed store
   meeting D, to a first-order value or an exception, is matched by a resource-free target run to
   the same value or exception, the target's final store related to the source's by GStore under
   a world fixing the old locations. *)
Theorem KTerm_adequacy : forall g e0 e rho s,
 D_wf -> KTerm g e0 e -> Forall (fun p => fo (snd p)) rho -> (forall x, In x g -> exists v, lookup x rho = Some v) ->
 StoreHas s -> store_ok s ->
 (forall v s0, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0) -> fo v ->
    exists s' w, srun (Cfg (Eval rho e) [] s) [] (Cfg (Ret v) [] s') /\ wext (id_world s) w /\ GStore w s' s0) /\
 (forall x s0, srun (Cfg (Eval rho e0) [] s) [] (Cfg (Throw x) [] s0) ->
    exists s' w, srun (Cfg (Eval rho e) [] s) [] (Cfg (Throw x) [] s') /\ wext (id_world s) w /\ GStore w s' s0).
Proof. intros g e0 e rho s Dw H. exact (JitKTermFund.JitKTermFund.adequacy sealed D g e e0 rho s Dw H). Qed.

(* Termination, by contraposition: a target with no resource-free run to a value or an exception
   has a source with none to a first-order value or an exception. Constructive. *)
Theorem KTerm_diverges : forall g e0 e rho s,
 D_wf -> KTerm g e0 e -> Forall (fun p => fo (snd p)) rho -> (forall x, In x g -> exists v, lookup x rho = Some v) ->
 StoreHas s -> store_ok s ->
 (forall c', srun (Cfg (Eval rho e) [] s) [] c' -> forall v s', c' <> Cfg (Ret v) [] s' /\ forall x, c' <> Cfg (Throw x) [] s') ->
 (forall v s0, fo v -> ~ srun (Cfg (Eval rho e0) [] s) [] (Cfg (Ret v) [] s0)) /\
 (forall x s0, ~ srun (Cfg (Eval rho e0) [] s) [] (Cfg (Throw x) [] s0)).
Proof.
 intros g e0 e rho s Dw H Hfo Hdom HS Hok N.
 destruct (KTerm_adequacy g e0 e rho s Dw H Hfo Hdom HS Hok) as [A B]. split.
 - intros v s0 Fv Sr. destruct (A v s0 Sr Fv) as (s' & w & S' & _). exact (proj1 (N _ S' v s') eq_refl).
 - intros x s0 Sr. destruct (B x s0 Sr) as (s' & w & S' & _). exact (proj2 (N _ S' VNil s') x eq_refl).
Qed.

(* Two links compose through the closed first-order observation, never by transitivity. *)
Theorem KTerm_compose : JitKRefTerm.JitKRefTerm.KTerm_compose_statement sealed D.
Proof.
 intros g b0 b1 e rho s Dw H01 H1e Hfo Hdom HS Hok.
 destruct (KTerm_adequacy g b0 b1 rho s Dw H01 Hfo Hdom HS Hok) as [A0 B0].
 destruct (KTerm_adequacy g b1 e rho s Dw H1e Hfo Hdom HS Hok) as [A1 B1]. split.
 - intros v s0 Sr Fv. destruct (A0 v s0 Sr Fv) as (s1 & w1 & S1 & W1 & G1).
   destruct (A1 v s1 S1 Fv) as (s' & w2 & S' & W2 & G2).
   exists s', (compose_world w2 w1). split; [exact S'|split].
   + apply JitKTermGround.JitKTermGround.wext_compose_id; assumption.
   + eapply JitKTermGround.JitKTermGround.GStore_trans; [exact (proj2 W2)|exact (proj2 W1)|exact G2|exact G1].
 - intros x s0 Sr. destruct (B0 x s0 Sr) as (s1 & w1 & S1 & W1 & G1).
   destruct (B1 x s1 S1) as (s' & w2 & S' & W2 & G2).
   exists s', (compose_world w2 w1). split; [exact S'|split].
   + apply JitKTermGround.JitKTermGround.wext_compose_id; assumption.
   + eapply JitKTermGround.JitKTermGround.GStore_trans; [exact (proj2 W2)|exact (proj2 W1)|exact G2|exact G1].
Qed.

(* ======================= source reduction ======================= *)
(* The source is the side whose runs ObsT quantifies over (JitKTerm.KRef's second expression).
   Under jit_rules_nr a silent step is the machine's only step from a configuration whose next
   move is MTau, so every source run passes through its reduct, and the reduct's relation gives
   the configuration's at the SAME index. *)
Lemma ObsT_red1 : forall k w c0 c c1, next_r R P c = MTau c1 -> ObsT k w c0 c1 -> ObsT k w c0 c.
Proof.
 intros k w c0 c c1 E H n t c' L Hr. inversion Hr as [c2|n' c2 l c3 t' c4 St Hr']; subst.
 - split; [|split].
   + intros v s Ec; subst. cbn in E. discriminate E.
   + intros x s Ec; subst. cbn in E. discriminate E.
   + intros why N. rewrite E in N. discriminate N.
 - destruct St as [c c3 E3|c q kk r E3|c r x _ Rx].
   + rewrite E in E3. injection E3 as <-. exact (H n' t' c' ltac:(lia) Hr').
   + rewrite E in E3. discriminate E3.
   + destruct r; discriminate Rx.
Qed.

Lemma ObsT_red : forall k w c0 c c1, srun c [] c1 -> ObsT k w c0 c1 -> ObsT k w c0 c.
Proof.
 intros k w c0 c c1 Hs. unfold JitKTerm.JitKTerm.srun in Hs. remember (@nil event) as t eqn:Et.
 induction Hs as [c|c l c2 t c3 St Hs IH]; intro H; [exact H|].
 destruct St as [c c2 E|c q kk r E|c r x _ Rx].
 - cbn in Et. apply (ObsT_red1 k w c0 c c2 E). exact (IH Et H).
 - cbn in Et. discriminate Et.
 - destruct r; discriminate Rx.
Qed.

Theorem ERel_red : forall k w rho0 e0 rho e,
 (forall j w' K s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s -> exists rho' e' s',
    srun (Cfg (Eval rho e) K s) [] (Cfg (Eval rho' e') K s') /\ SRel j w' s0 s' /\ ERel j w' rho0 e0 rho' e') ->
 ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e H. apply (JitKTermBase.JitKTermBase.ERel_iff sealed D). intros j L w' W K0 K HK s0 s HS.
 destruct (H j w' K s0 s L W HS) as (rho' & e' & s' & S' & HS' & He).
 eapply ObsT_red; [exact S'|].
 eapply (JitKTermBase.JitKTermBase.ERel_apply sealed D); [exact He|apply le_n| |exact HK|exact HS'].
 eapply JitKTermBase.JitKTermBase.wext_self; exact HS'.
Qed.

Corollary ERel_red_same : forall k w rho0 e0 rho e rho' e',
 (forall K s, srun (Cfg (Eval rho e) K s) [] (Cfg (Eval rho' e') K s)) ->
 ERel k w rho0 e0 rho' e' -> ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e rho' e' Hs He. apply ERel_red. intros j w' K s0 s L W HS.
 exists rho', e', s. split; [apply Hs|split; [exact HS|]].
 eapply JitKTermBase.JitKTermBase.ERel_mono; [exact L|exact W|exact He].
Qed.

Lemma srun_tau : forall c c' t c'', next_r R P c = MTau c' -> srun c' t c'' -> srun c t c''.
Proof. exact (JitKTermBase.JitKTermBase.srun_tau sealed). Qed.
Lemma srun_refl : forall c, srun c [] c.
Proof. exact (JitKTermBase.JitKTermBase.srun_refl sealed). Qed.
Lemma sval_next : forall rho a v K s, sval rho a = Some v -> next_r R P (Cfg (Eval rho a) K s) = MTau (Cfg (Ret v) K s).
Proof. exact (JitKTermBase.JitKTermBase.sval_next sealed). Qed.

Theorem ERel_red_let : forall k w rho0 e0 x a b v rho, sval rho a = Some v ->
 ERel k w rho0 e0 ((x, v) :: rho) b -> ERel k w rho0 e0 rho (ELet x a b).
Proof.
 intros k w rho0 e0 x a b v rho Hv He. eapply ERel_red_same; [|exact He]. intros K s.
 eapply srun_tau; [reflexivity|]. eapply srun_tau; [apply sval_next; exact Hv|].
 eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

Theorem ERel_red_if : forall k w rho0 e0 c a b bv rho, sval rho c = Some (VBool bv) ->
 ERel k w rho0 e0 rho (if bv then a else b) -> ERel k w rho0 e0 rho (EIf c a b).
Proof.
 intros k w rho0 e0 c a b bv rho Hv He. destruct bv; (eapply ERel_red_same; [|exact He]); intros K s;
 (eapply srun_tau; [reflexivity|]); (eapply srun_tau; [apply sval_next; exact Hv|]);
 (eapply srun_tau; [reflexivity|apply srun_refl]).
Qed.

Theorem ERel_red_cond : forall k w rho0 e0 c b rest bv rho, sval rho c = Some (VBool bv) ->
 ERel k w rho0 e0 rho (if bv then b else ECond rest) -> ERel k w rho0 e0 rho (ECond ((c, b) :: rest)).
Proof.
 intros k w rho0 e0 c b rest bv rho Hv He. destruct bv; (eapply ERel_red_same; [|exact He]); intros K s;
 (eapply srun_tau; [reflexivity|]); (eapply srun_tau; [apply sval_next; exact Hv|]);
 (eapply srun_tau; [reflexivity|apply srun_refl]).
Qed.

Theorem ERel_red_type : forall k w rho0 e0 a rho, ERel k w rho0 e0 rho a -> ERel k w rho0 e0 rho (EType a).
Proof.
 intros k w rho0 e0 a rho He. eapply ERel_red_same; [|exact He]. intros K s.
 eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

(* Inlining a sealed callee: the source calls f, a definition in D, with atomic arguments; the
   target is related to the callee's body in the callee's environment. *)
Theorem ERel_red_call : forall k w rho0 e0 f ps b args vs rho, In (f, FUser ps b) D ->
 Forall2 (fun a u => sval rho a = Some u) args vs -> List.length vs = List.length ps ->
 ERel k w rho0 e0 (combine ps vs) b -> ERel k w rho0 e0 rho (ECall f args).
Proof.
 intros k w rho0 e0 f ps b args vs rho I F L He. apply ERel_red. intros j w' K s0 s Lj W HS.
 assert (Ef : lookup f (gfuns s) = Some (FUser ps b)) by (destruct HS as (_ & _ & H1 & _); apply H1; exact I).
 exists (combine ps vs), b, s. split; [|split; [exact HS|eapply JitKTermBase.JitKTermBase.ERel_mono; eauto]].
 destruct F as [|a u args vs Ha F].
 - apply (srun_tau _ (Cfg (Eval (combine ps []) b) K s));
     [exact (JitKTermBase.JitKTermBase.call_named_user sealed f ps b [] K s Ef L)|apply srun_refl].
 - eapply srun_tau; [reflexivity|]. eapply srun_tau; [apply sval_next; exact Ha|].
   apply (JitKTermBase.JitKTermBase.srun_callargs sealed) with (vs := vs); [exact F|].
   apply (JitKTermBase.JitKTermBase.call_named_user sealed); [exact Ef|exact L].
Qed.

(* A cell only the source has: SRel relates only the world's cells. *)
Theorem SRel_with_cell_r : forall k w s0 s, SRel k w s0 s -> SRel k w s0 (with_cell s).
Proof.
 intros k w s0 s (W & H0 & H1 & G & Gv & Hp).
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact G|split; [exact Gv|]]]]].
 intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. split; [exact N0|split; [|exact F]].
 cbn. rewrite nth_error_app1; [exact N|]. apply nth_error_Some. congruence.
Qed.

(* ((lambda x b) a) with a atomic: the closure takes a fresh cell on the source side only. *)
Theorem ERel_red_app_lam : forall k w rho0 e0 x b a v rho, sval rho a = Some v ->
 (forall l, ERel k w rho0 e0 ((x, v) :: (id_key, VVec l) :: rho) b) ->
 ERel k w rho0 e0 rho (EApp (ELam x b) [a]).
Proof.
 intros k w rho0 e0 x b a v rho Hv He. apply ERel_red. intros j w' K s0 s L W HS.
 exists ((x, v) :: (id_key, VVec (List.length (heap s))) :: rho), b, (with_cell s).
 split; [|split; [apply SRel_with_cell_r; exact HS|eapply JitKTermBase.JitKTermBase.ERel_mono; eauto]].
 eapply srun_tau; [reflexivity|]. eapply srun_tau; [reflexivity|]. eapply srun_tau; [reflexivity|].
 eapply srun_tau; [apply sval_next; exact Hv|]. eapply srun_tau; [reflexivity|apply srun_refl].
Qed.

(* ======================= a front rule: lambda application to let ======================= *)
(* An atom in scope g: a literal, or a variable of g. *)
Definition atom_in (g : list name) (a : expr) : bool :=
 match a with EVar y => bound g y | _ => match lit_val a with Some _ => true | None => false end end.

Lemma atom_rel : forall k w g rho0 rho a, EnvRel_with (VRel k) w g rho0 rho -> atom_in g a = true ->
 exists v0 v, sval rho0 a = Some v0 /\ sval rho a = Some v /\ VRel k w v0 v.
Proof.
 intros k w g rho0 rho a HE A.
 assert (Lit : forall v, lit_val a = Some v -> exists v0 v', sval rho0 a = Some v0 /\ sval rho a = Some v' /\ VRel k w v0 v').
 { intros v Lv. exists v, v. split; [apply JitKTermCompatCtl.JitKTermCompatCtl.lit_sval; exact Lv|].
   split; [apply JitKTermCompatCtl.JitKTermCompatCtl.lit_sval; exact Lv|].
   exact (JitKTermCompatCtl.JitKTermCompatCtl.VRel_lit sealed D k w a v Lv). }
 destruct a; cbn in A; try discriminate; try (eapply Lit; reflexivity).
 unfold bound in A. apply existsb_exists in A as [y [Iy Ey]]. apply text_eqb_eq in Ey. subst y.
 exact (HE x Iy).
Qed.

(* norm's ((lambda X B) A) to (let X A B'), for an atomic A, checked as a compatibility rule:
   B' must refine B for termination in scope X :: g. id_key (KLPort's closure-identity key) must
   not be in scope: the source's body sees the closure's identity cell under it, the target's
   does not. *)
Theorem KTerm_lambda_app : forall g x a b0 b, atom_in g a = true -> ~ In id_key g ->
 KTerm (x :: g) b0 b -> KTerm g (EApp (ELam x b0) [a]) (ELet x a b).
Proof.
 intros g x a b0 b A Nk Hb k w rhoT rhoS W HE.
 destruct (atom_rel k w g rhoT rhoS a HE A) as (vT & vS & ET & ES & HV).
 apply (ERel_red_app_lam k w rhoT (ELet x a b) x b0 a vS rhoS ES). intro l.
 apply (JitKTermBase.JitKTermBase.ERel_anti_let sealed D k w x a b vT rhoT); [exact ET|].
 apply Hb; [exact W|]. intros y Iy. cbn [lookup]. destruct (text_eqb y x) eqn:Ey.
 - exists vT, vS. auto.
 - destruct Iy as [<-|Iy]; [rewrite text_eqb_refl in Ey; discriminate|].
   destruct (text_eqb y id_key) eqn:Ek.
   + apply text_eqb_eq in Ek. subst y. contradiction.
   + exact (HE y Iy).
Qed.
End Term.
End JitKRefTermThm.
