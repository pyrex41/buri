(* Shen/JIT Phase 2, r1-f-sugar: the norm checkers of four front families of src/lowerer/lower.shen
   (934cfa5), each proved sound for KRef (rocq/JitKRef.v) from the source to its rewrite:
   - cond (norm-cond): a clause whose test is the literal true ends the chain; any other clause
     becomes an if whose else is the rest of the chain. [prim raise-cond []] erases to ECond [], so
     the empty chain is congruence.
   - sugar: (type X T) is X; (protect X) is X (the kernel's protect, sys.kl (defun protect (V) V),
     in D: JitFrontD.D_has_kernel_protect); ((lambda X B) A) is (let X A B).
   - thaw sugar: (thaw X) is [apply X], which erases to EApp X [] (the kernel's thaw,
     (defun thaw (V) (V)), in D: JitFrontD.D_has_kernel_thaw).
   - trap sugar: (trap-error X H) with H not a lambda is [trap X E [apply H [var E]]], E fresh,
     which erases to ETrap X (ELam E (EApp H [EVar E])). (trap-error X (lambda E H)) is [trap X E H],
     which erases back to the source shape, so it is congruence (compat_trap, compat_lambda).

   How the checkers compose (the Phase 2 front design). Every checker takes the recursive checker
   `rec` as a parameter (open recursion). A rule is a source anti-reduction to an intermediate
   source term followed by `rec` on that intermediate:
     type      (EType a0)                    ~> a0                 then rec g a0 e
     protect   (ECall protect [a0])          ~> a0                 then rec g a0 e
     cond-true (ECond ((true, b0) :: _))     ~> b0                 then rec g b0 e
   For four rules the checker takes the intermediate's congruence step itself, so the rule is
   checked and proved as the anti-reduction composed with that congruence step:
     cond-if   (ECond ((c0, b0) :: rest0))   ~> EIf c0 b0 (ECond rest0), then if-congruence
     thaw      (ECall thaw [a0])             ~> EApp a0 [],         then app-congruence
     lam-app   (EApp (ELam x b0) [a0])       ~> ELet x a0 b0,       then let-congruence
     trap-eta  (ETrap a0 h0)                 ~> ETrap a0 (ELam e (EApp h0 [EVar e])), then trap,
                                                lambda, app and var congruence
   INTERFACE LIMIT of these four. Where another family rewrites the intermediate at the same node,
   this checker rejects, and that family's rule must take the source form as its input: copy's
   let-lambda rewrites the let lam-app makes; copy's frozen-late rewrites the
   [if C1 Y1 [if C2 Y2 [const false]]] chain norm-cond makes; copy's frozen-in and inline's
   thaw-with replace the [apply [var G]] thaw sugar makes. (No rule rewrites a trap at its node.)
   The plain anti-reductions (type, protect, cond-true) have no such limit: rec runs on the
   intermediate itself. The composed forms are the *_statement Definitions below; each is proved
   (the theorems below), with no hypothesis beyond its premises.

   Soundness of the combined checker chk_front (congruence + the four families, by fuel) is proved
   first under Section hypotheses naming the KRef compatibility statements and the rule statements
   (chk_front_sound_h), then instantiated with the proved theorems (chk_front_sound): no hypothesis
   remains but D_wf.

   What the checkers REJECT, and why (each pinned by an Example; NOT a refutation unless stated):
   - ((fn F) X ...) to (F X ...): JitKRef.v's design notes (the kernel's fn is not accepted code
     under Com's FunRel; the open form calls shen-jit.arity?, which the store does not define).
   - eval-kl to a call of shen-jit.eval-kl (JitKRef.v's design notes: the store does not define it).
   - curried dynamic application, (F A B) to ((F A) B): under jit_rules arity_errors is on, so a
     partial application VPartial g [] applied to one of g's two arguments raises XArity where the
     source call with both runs g; and the target applies (F A) before evaluating B. Not accepted;
     the counterexample is argued here, not proved in Rocq (UNKNOWN as a Rocq fact).
   - ((lambda X B) A M ...) to ((let X A B) M ...): the source evaluates M before B, the target B
     before M (both may raise). Not accepted; argued, not proved in Rocq.
     Both are deferred to the owner of the dynamic-application uncurrying family.
   - lam-app and trap-eta in a scope that holds KLPort.id_key, and trap-eta when the fresh name is
     in scope: the source's closure cell binds id_key (lam-app), the target's handler binds the
     fresh name and id_key (trap-eta), shadowing a scoped name.

   Census (spikes/pass-split/FEATURES.md, census, not proof): fam:cond is needed by 462
   definitions, fam:thaw-sugar by 37, fam:trap-sugar by 36, fam:sugar by 4. No count of validated
   definitions changes here: no norm-link judge runs these checkers on the stage 0 witnesses yet
   (the full-pipeline count is UNKNOWN).
   No axioms, nothing Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatClo JitKRefPrim JitKRefCompatCtl JitKRefCompatCall JitKRefFv JitKRefFund JitLowerStage0 JitNorm JitNormStage0 JitFrontD.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontSugar.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitLowerPrim.JitLowerPrim
 JitLowerStep.JitLowerStep JitLowerThm.JitLowerThm JitLowerCheck.JitLowerCheck JitKRef.JitKRef
 JitKRefGround.JitKRefGround JitKRefBase.JitKRefBase.

Definition thaw_name : name := JitFrontD.JitFrontD.thaw_name.
Definition protect_name : name := JitFrontD.JitFrontD.protect_name.

(* ---------- generic helpers ---------- *)
Fixpoint all2 {A B} (f : A -> B -> bool) (l0 : list A) (l : list B) : bool := match l0, l with
 | [], [] => true | a :: l0, b :: l => f a b && all2 f l0 l | _, _ => false end.

Lemma all2_Forall2 : forall {A B} (f : A -> B -> bool) (Q : A -> B -> Prop),
 (forall a b, f a b = true -> Q a b) -> forall l0 l, all2 f l0 l = true -> Forall2 Q l0 l.
Proof.
 intros A B f Q Hf. induction l0 as [|a l0 IH]; destruct l as [|b l]; cbn; intro H; try discriminate.
 - constructor.
 - apply andb_true_iff in H as [H1 H2]. constructor; [apply Hf; exact H1|apply IH; exact H2].
Qed.

Lemma lookup_In_gen : forall {A} x (l : list (name * A)) v, lookup x l = Some v -> In (x, v) l.
Proof.
 intros A x l v. induction l as [|[y u] l IH]; cbn; intro H; [discriminate|].
 destruct (text_eqb x y) eqn:E.
 - apply text_eqb_eq in E. subst. injection H as <-. left. reflexivity.
 - right. apply IH. exact H.
Qed.

Lemma bound_true : forall g x, bound g x = true -> In x g.
Proof.
 intros g x H. unfold bound in H. apply existsb_exists in H as (y & I & E).
 apply text_eqb_eq in E. subst. exact I.
Qed.

Lemma bound_false : forall g x, bound g x = false -> ~ In x g.
Proof.
 intros g x H I. unfold bound in H.
 assert (existsb (text_eqb x) g = true) by (apply existsb_exists; exists x; split; [exact I|apply text_eqb_refl]).
 congruence.
Qed.

Definition num_eqb' (a b : num) : bool := match a, b with
 | NInt x, NInt y => Z.eqb x y | NFloat x, NFloat y => N.eqb x y | _, _ => false end.

(* Two equal literals. *)
Definition lit_eqb (e0 e : expr) : bool := match e0, e with
 | ENum a, ENum b => num_eqb' a b | EStr a, EStr b => text_eqb a b | ESym a, ESym b => text_eqb a b
 | EBool a, EBool b => Bool.eqb a b | ENil, ENil => true | _, _ => false end.

Lemma lit_eqb_spec : forall e0 e, lit_eqb e0 e = true -> e0 = e /\ exists v, lit_val e0 = Some v.
Proof.
 intros e0 e H. destruct e0; destruct e; cbv beta iota delta [lit_eqb] in H; try discriminate.
 - unfold num_eqb' in H. destruct n, n0; cbv beta iota in H; try discriminate.
   + apply Z.eqb_eq in H. subst. split; [reflexivity|eexists; reflexivity].
   + apply N.eqb_eq in H. subst. split; [reflexivity|eexists; reflexivity].
 - apply text_eqb_eq in H. subst. split; [reflexivity|eexists; reflexivity].
 - apply text_eqb_eq in H. subst. split; [reflexivity|eexists; reflexivity].
 - apply Bool.eqb_prop in H. subst. split; [reflexivity|eexists; reflexivity].
 - split; [reflexivity|eexists; reflexivity].
Qed.

Definition is_true_lit (e : expr) : bool := match e with EBool true => true | _ => false end.

Lemma is_true_lit_eq : forall e, is_true_lit e = true -> e = EBool true.
Proof. intros e H. destruct e; cbv beta iota delta [is_true_lit] in H; try discriminate. destruct b; [reflexivity|discriminate]. Qed.

(* A checker: scope, source, target. *)
Definition Chk := list name -> expr -> expr -> bool.

Section Equiv.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation ObsT := (JitKRef.JitKRef.ObsT sealed).
Notation EnvRel_with := JitKRef.JitKRef.EnvRel_with.
Notation VRel := (JitKRef.JitKRef.VRel sealed D).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation KRel := (JitKRef.JitKRef.KRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation fund_below := (JitKRef.JitKRef.fund_below sealed D).
Notation AppAll := (JitKRefBase.JitKRefBase.AppAll sealed D).
Notation nonterm := (JitKRefBase.JitKRefBase.nonterm sealed).
Notation VRel_unfold := (JitKRefGround.JitKRefGround.VRel_unfold sealed D).
Notation KRel_iff := (JitKRefBase.JitKRefBase.KRel_iff sealed D).
Notation ERel_iff := (JitKRefBase.JitKRefBase.ERel_iff sealed D).
Notation KRel_throw := (JitKRefBase.JitKRefBase.KRel_throw sealed D).
Notation KRel_ret := (JitKRefBase.JitKRefBase.KRel_ret sealed D).
Notation KRel_down := (JitKRefBase.JitKRefBase.KRel_down sealed D).
Notation KRel_mono := (JitKRefBase.JitKRefBase.KRel_mono sealed D).
Notation KRel_push := (JitKRefBase.JitKRefBase.KRel_push sealed D).
Notation KRel_KHead := (JitKRefBase.JitKRefBase.KRel_KHead sealed D).
Notation KRel_throw_frame := (JitKRefBase.JitKRefBase.KRel_throw_frame sealed D).
Notation ret_frame_tau := (JitKRefBase.JitKRefBase.ret_frame_tau sealed D).
Notation SRel_down := (JitKRefBase.JitKRefBase.SRel_down sealed D).
Notation SRel_with_cell := (JitKRefBase.JitKRefBase.SRel_with_cell sealed D).
Notation ERel_apply := (JitKRefBase.JitKRefBase.ERel_apply sealed D).
Notation ERel_push := (JitKRefBase.JitKRefBase.ERel_push sealed D).
Notation ERel_at := (JitKRefBase.JitKRefBase.ERel_at sealed D).
Notation throw_at := (JitKRefBase.JitKRefBase.throw_at sealed D).
Notation ret_at := (JitKRefBase.JitKRefBase.ret_at sealed D).
Notation ERel_anti_type := (JitKRefBase.JitKRefBase.ERel_anti_type sealed D).
Notation ERel_anti_cond := (JitKRefBase.JitKRefBase.ERel_anti_cond sealed D).
Notation VRel_asbool := (JitKRefBase.JitKRefBase.VRel_asbool sealed D).
Notation wext_self := (JitKRefBase.JitKRefBase.wext_self sealed D).
Notation EnvRel_mono := (JitKRefBase.JitKRefBase.EnvRel_mono sealed D).
Notation AppAll_mono := (JitKRefBase.JitKRefBase.AppAll_mono sealed D).
Notation ObsT_running := (JitKRefBase.JitKRefBase.ObsT_running sealed).
Notation ObsT_step := (JitKRefBase.JitKRefBase.ObsT_step sealed).
Notation ObsT_anti := (JitKRefBase.JitKRefBase.ObsT_anti sealed).
Notation ObsT_anti_io := (JitKRefBase.JitKRefBase.ObsT_anti_io sealed).
Notation ObsT_swap := (JitKRefBase.JitKRefBase.ObsT_swap sealed).
Notation ObsT_0 := (JitKRefBase.JitKRefBase.ObsT_0 sealed).
Notation srun_tau := (JitKRefBase.JitKRefBase.srun_tau sealed).
Notation srun_refl := (JitKRefBase.JitKRefBase.srun_refl sealed).
Notation step_r_cases := (JitKRefBase.JitKRefBase.step_r_cases sealed).
Notation sval_next := (JitKRefBase.JitKRefBase.sval_next sealed).
Notation throw_frame_next := (JitKRefBase.JitKRefBase.throw_frame_next sealed).
Notation call_named_user := (JitKRefBase.JitKRefBase.call_named_user sealed).
Notation next_KIf := (JitKRefBase.JitKRefBase.next_KIf sealed).
Notation next_KCond := (JitKRefBase.JitKRefBase.next_KCond sealed).
Notation next_KLet := (JitKRefBase.JitKRefBase.next_KLet sealed).
Notation next_KHead_cons := (JitKRefBase.JitKRefBase.next_KHead_cons sealed).
Notation next_KTrap_ret := (JitKRefBase.JitKRefBase.next_KTrap_ret sealed).
Notation next_KTrap_throw := (JitKRefBase.JitKRefBase.next_KTrap_throw sealed).
Notation env_cons := (JitKRefCompatCtl.JitKRefCompatCtl.env_cons sealed D).
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

(* ======================= the rule statements ======================= *)
Definition sugar_type_statement : Prop := forall g a0 e, KRef g a0 e -> KRef g (EType a0) e.
Definition sugar_protect_statement : Prop := forall g a0 e,
 JitFrontD.JitFrontD.D_has_kernel_protect D -> KRef g a0 e -> KRef g (ECall protect_name [a0]) e.
Definition sugar_lamapp_statement : Prop := forall g x a0 a b0 b,
 ~ In id_key g -> KRef g a0 a -> KRef (x :: g) b0 b -> KRef g (EApp (ELam x b0) [a0]) (ELet x a b).
Definition cond_true_statement : Prop := forall g b0 rest0 e,
 KRef g b0 e -> KRef g (ECond ((EBool true, b0) :: rest0)) e.
Definition cond_if_statement : Prop := forall g c0 c b0 b rest0 r,
 KRef g c0 c -> KRef g b0 b -> KRef g (ECond rest0) r -> KRef g (ECond ((c0, b0) :: rest0)) (EIf c b r).
Definition thaw_sugar_statement : Prop := forall g a0 a, D_wf ->
 JitFrontD.JitFrontD.D_has_kernel_thaw D -> KRef g a0 a -> KRef g (ECall thaw_name [a0]) (EApp a []).
Definition trap_sugar_statement : Prop := forall g a0 a h0 h x, D_wf -> ~ In x g -> ~ In id_key g ->
 KRef g a0 a -> KRef g h0 h -> KRef g (ETrap a0 h0) (ETrap a (ELam x (EApp h [EVar x]))).

(* ======================= helpers ======================= *)
Lemma fb_all : D_wf -> forall k, fund_below k.
Proof. intros Dw k j Lj. apply (JitKRefFund.JitKRefFund.fund_gen sealed D Dw k). lia. Qed.

Lemma appall : D_wf -> forall k w K0 K, KRel k w K0 K -> AppAll k w K0 K.
Proof.
 intros Dw k w K0 K HK. exact (JitKRefCompatClo.JitKRefCompatClo.app_rel sealed D k w K0 K (fb_all Dw k)
   (JitKRefPrim.JitKRefPrim.prim_compat sealed D) HK).
Qed.

Lemma EnvRel_skip_src : forall j w g rho0 rho y u, EnvRel_with (VRel j) w g rho0 rho -> ~ In y g ->
 EnvRel_with (VRel j) w g ((y, u) :: rho0) rho.
Proof.
 intros j w g rho0 rho y u HE N x Ix. cbn [lookup]. destruct (text_eqb x y) eqn:E.
 - apply text_eqb_eq in E. subst. contradiction.
 - apply HE. exact Ix.
Qed.

Lemma EnvRel_skip_tgt : forall j w g rho0 rho y u, EnvRel_with (VRel j) w g rho0 rho -> ~ In y g ->
 EnvRel_with (VRel j) w g rho0 ((y, u) :: rho).
Proof.
 intros j w g rho0 rho y u HE N x Ix. cbn [lookup]. destruct (text_eqb x y) eqn:E.
 - apply text_eqb_eq in E. subst. contradiction.
 - apply HE. exact Ix.
Qed.

(* A cell only the target allocated: the world does not name it. *)
Theorem SRel_with_cell_r : forall k w s0 s, SRel k w s0 s -> SRel k w s0 (with_cell s).
Proof.
 intros k w s0 s (W & H0 & H1 & G & Gv & Hp).
 split; [exact W|split; [exact H0|split; [exact H1|split; [exact G|split; [exact Gv|]]]]].
 intros l0 l I. destruct (Hp _ _ I) as (c0 & c & N0 & N & F). exists c0, c. split; [exact N0|split; [|exact F]].
 cbn. rewrite nth_error_app1; [exact N|]. apply nth_error_Some. congruence.
Qed.

(* The bind lemma with a source that takes any silent path, possibly changing its store in a way
   SRel tolerates, to its subexpression under a built continuation. *)
Theorem ERel_push_src : forall k w rho0 e0 rho e e0' rho' e' (F0 : list frame -> store -> list frame)
 (st0 : store -> store) (F : list frame -> list frame),
 (forall K0 s0, srun (Cfg (Eval rho0 e0) K0 s0) [] (Cfg (Eval rho0 e0') (F0 K0 s0) (st0 s0))) ->
 (forall K s, next_r R P (Cfg (Eval rho e) K s) = MTau (Cfg (Eval rho' e') (F K) s)) ->
 (forall j w' s0 s, SRel j w' s0 s -> SRel j w' (st0 s0) s) ->
 (forall j w' K0 K s0, (j < k)%nat -> wext w w' -> KRel j w' K0 K -> KRel j w' (F0 K0 s0) (F K)) ->
 (forall j w', (j < k)%nat -> wext w w' -> ERel j w' rho0 e0' rho' e') ->
 ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e e0' rho' e' F0 st0 F E0 E Hs HF He. apply ERel_iff.
 intros j L w' W K0 K HK s0 s HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_running.
 - reflexivity.
 - unfold JitKRefBase.JitKRefBase.nonterm. rewrite E. exact I.
 - intros x. cbn [kont mem]. apply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite E in E1. injection E1 as <-. eexists; split; [apply E0|].
   eapply ERel_apply; [apply (He j w'); [lia|exact W]|apply le_n|eapply wext_self; exact HS| |].
   + apply HF; [lia|exact W|eapply KRel_down; [|exact HK]; lia].
   + apply Hs. eapply SRel_down; [|exact HS]; lia.
 - intros q kk r E1. rewrite E in E1. discriminate.
Qed.

(* ======================= type and cond-true: plain anti-reduction ======================= *)
Theorem sugar_type : sugar_type_statement.
Proof. intros g a0 e H k w rho0 rho W HE. apply ERel_anti_type. apply H; assumption. Qed.

Theorem cond_true : cond_true_statement.
Proof.
 intros g b0 rest0 e H k w rho0 rho W HE. apply (ERel_anti_cond k w (EBool true) b0 rest0 true); [reflexivity|].
 apply H; assumption.
Qed.

(* ======================= cond to if ======================= *)
Theorem KRel_KCond_KIf : forall k w b0 rest0 rho0 b r rho K0 K, KRel k w K0 K ->
 ERel k w rho0 b0 rho b -> ERel k w rho0 (ECond rest0) rho r ->
 KRel k w (KCond b0 rest0 rho0 :: K0) (KIf b r rho :: K).
Proof.
 intros k w b0 rest0 rho0 b r rho K0 K HK Hb Hr. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KIf in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KCond|apply srun_refl]|].
   rewrite (VRel_asbool _ _ _ _ HV). destruct (JitKRefBase.JitKRefBase.asbool v) as [[|]|].
   + eapply ERel_at; eauto.
   + eapply ERel_at; eauto.
   + eapply throw_at; eauto.
 - intros v s. eexists. apply next_KIf.
Qed.

Theorem cond_if : cond_if_statement.
Proof.
 intros g c0 c b0 b rest0 r Hc Hb Hr k w rho0 rho W HE.
 apply (ERel_push k w rho0 (ECond ((c0, b0) :: rest0)) rho (EIf c b r) rho0 c0 rho c
   (fun K0 => KCond b0 rest0 rho0 :: K0) (fun K => KIf b r rho :: K)).
 - intros K0 s0. reflexivity.
 - intros K s. reflexivity.
 - intros j w' K0 K Lj W' HK. apply KRel_KCond_KIf; [exact HK| |].
   + apply Hb; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
   + apply Hr; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
 - intros j w' Lj W'. apply Hc; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
Qed.

(* ======================= protect ======================= *)
(* The kernel's protect frame returns the value it is given, and lets an exception through. *)
Theorem KRel_protect : forall k w p rho0 K0 K, In (protect_name, FUser [p] (EVar p)) D -> KRel k w K0 K ->
 KRel k w (KCallArgs protect_name [] [] rho0 :: K0) K.
Proof.
 intros k w p rho0 K0 K I HK. apply KRel_iff. intros j L w' W. split.
 - intros v0 v s0 s HV HS.
   assert (Ef : lookup protect_name (gfuns s0) = Some (FUser [p] (EVar p))) by (destruct HS as (_ & H0 & _); apply H0; exact I).
   eapply ObsT_anti; [|eapply KRel_ret; [eapply KRel_mono; [exact L|exact W|exact HK]|exact HV|exact HS]].
   apply (srun_tau _ (Cfg (Eval [(p, v0)] (EVar p)) K0 s0)).
   + exact (call_named_user protect_name [p] (EVar p) [v0] K0 s0 Ef eq_refl).
   + eapply srun_tau; [apply (sval_next _ _ v0); cbn [JitKRefBase.JitKRefBase.sval lookup]; rewrite text_eqb_refl; reflexivity|apply srun_refl].
 - intros x s0 s HS. eapply ObsT_anti; [eapply srun_tau; [apply throw_frame_next; reflexivity|apply srun_refl]|].
   eapply KRel_throw; [eapply KRel_mono; [exact L|exact W|exact HK]|exact HS].
Qed.

Theorem sugar_protect : sugar_protect_statement.
Proof.
 intros g a0 e [p I] H k w rho0 rho W HE. apply ERel_iff. intros j L w' W' K0 K HK s0 s HS.
 eapply ObsT_anti; [eapply srun_tau; [reflexivity|apply srun_refl]|].
 eapply ERel_apply; [apply H; [exact W|exact HE]|exact L|exact W'| |exact HS].
 apply (KRel_protect j w' p rho0 K0 K I HK).
Qed.

(* ======================= lambda application ======================= *)
Theorem KRel_lamapp : forall k w x b0 rho0' b rho K0 K, KRel k w K0 K ->
 (forall j w' v0 v, (j <= k)%nat -> wext w w' -> VRel j w' v0 v -> ERel j w' ((x, v0) :: rho0') b0 ((x, v) :: rho) b) ->
 forall rho0, KRel k w (KArgs (VLam x b0 rho0') [] [] rho0 :: K0) (KLet x b rho :: K).
Proof.
 intros k w x b0 rho0' b rho K0 K HK Hb rho0. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' v0 v s0 s c1 L W HV HS E. rewrite next_KLet in E. injection E as <-.
   exists (Cfg (Eval ((x, v0) :: rho0') b0) K0 s0). split; [eapply srun_tau; [reflexivity|apply srun_refl]|].
   eapply (ERel_at (S j)); [apply le_n|eapply wext_self; exact HS|apply Hb; [exact L|exact W|exact HV]| |exact HS].
   eapply KRel_mono; [exact L|exact W|exact HK].
 - intros v s. eexists. apply next_KLet.
Qed.

Theorem sugar_lamapp : sugar_lamapp_statement.
Proof.
 intros g x a0 a b0 b Nid Ha Hb k w rho0 rho W HE.
 apply (ERel_push_src k w rho0 (EApp (ELam x b0) [a0]) rho (ELet x a b) a0 rho a
   (fun K0 s0 => KArgs (VLam x b0 (tagged_env rho0 s0)) [] [] rho0 :: K0) with_cell (fun K => KLet x b rho :: K)).
 - intros K0 s0. eapply srun_tau; [reflexivity|]. eapply srun_tau; [reflexivity|].
   eapply srun_tau; [reflexivity|apply srun_refl].
 - intros K s. reflexivity.
 - intros j w' s0 s HS. apply SRel_with_cell. exact HS.
 - intros j w' K0 K s0 Lj W' HK. apply KRel_lamapp; [exact HK|].
   intros i w'' v0 v Li W'' HV. apply Hb; [exact (proj2 W'')|].
   apply env_cons; [|exact HV]. unfold tagged_env. apply EnvRel_skip_src; [|exact Nid].
   eapply EnvRel_mono; [|eapply wext_trans; [exact W'|exact W'']|exact HE]; lia.
 - intros j w' Lj W'. apply Ha; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
Qed.

(* ======================= thaw ======================= *)
(* The kernel's thaw frame against the zero-argument application frame: the source calls thaw,
   whose body applies its argument to nothing, which is the target's application. *)
Theorem KRel_thaw : forall k w v rho0 rho K0 K, In (thaw_name, FUser [v] (EApp (EVar v) [])) D ->
 KRel k w K0 K -> AppAll k w K0 K -> KRel k w (KCallArgs thaw_name [] [] rho0 :: K0) (KHead [] rho :: K).
Proof.
 intros k w v rho0 rho K0 K I HK HA. apply KRel_push; [exact HK|reflexivity|reflexivity|].
 intros j w' f0 f s0 s L W HV HS.
 assert (Ef : lookup thaw_name (gfuns s0) = Some (FUser [v] (EApp (EVar v) []))) by (destruct HS as (_ & H0 & _); apply H0; exact I).
 eapply ObsT_anti.
 - apply (srun_tau _ (Cfg (Eval [(v, f0)] (EApp (EVar v) [])) K0 s0)).
   + exact (call_named_user thaw_name [v] (EApp (EVar v) []) [f0] K0 s0 Ef eq_refl).
   + eapply srun_tau; [reflexivity|].
     eapply srun_tau; [apply (sval_next _ _ f0); cbn [JitKRefBase.JitKRefBase.sval lookup]; rewrite text_eqb_refl; reflexivity|apply srun_refl].
 - apply KRel_ret; [|exact HV|exact HS].
   apply KRel_KHead; [eapply KRel_mono; [exact L|exact W|exact HK]|eapply AppAll_mono; [exact L|exact W|exact HA]|constructor].
Qed.

Theorem thaw_sugar : thaw_sugar_statement.
Proof.
 intros g a0 a Dw [v I] Ha k w rho0 rho W HE.
 apply (ERel_push k w rho0 (ECall thaw_name [a0]) rho (EApp a []) rho0 a0 rho a
   (fun K0 => KCallArgs thaw_name [] [] rho0 :: K0) (fun K => KHead [] rho :: K)).
 - intros K0 s0. reflexivity.
 - intros K s. reflexivity.
 - intros j w' K0 K Lj W' HK. eapply KRel_thaw; [exact I|exact HK|apply appall; [exact Dw|exact HK]].
 - intros j w' Lj W'. apply Ha; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
Qed.

(* ======================= trap with a handler that is not a lambda ======================= *)
Lemma next_lam : forall rho x b K s,
 next_r R P (Cfg (Eval rho (ELam x b)) K s) = MTau (Cfg (Ret (VLam x b (tagged_env rho s))) K (with_cell s)).
Proof. reflexivity. Qed.
Lemma next_ret_lam_exn : forall x b rho' y K s,
 next_r R P (Cfg (Ret (VLam x b rho')) (KApply [VExn y] :: K) s) = MTau (Cfg (Eval ((x, VExn y) :: rho') b) K s).
Proof. reflexivity. Qed.
Lemma next_app : forall rho h args K s,
 next_r R P (Cfg (Eval rho (EApp h args)) K s) = MTau (Cfg (Eval rho h) (KHead args rho :: K) s).
Proof. reflexivity. Qed.

Lemma VRel_exn : forall k w x, VRel k w (VExn x) (VExn x).
Proof. intros k w x. rewrite (VRel_unfold k). reflexivity. Qed.

(* The source applies the handler's value to the exception; the target evaluates the variable the
   exception is bound to first, then applies. *)
Lemma KRel_apply_head : forall k w x e env' K0 K, KRel k w K0 K -> AppAll k w K0 K -> lookup e env' = Some (VExn x) ->
 KRel k w (KApply [VExn x] :: K0) (KHead [EVar e] env' :: K).
Proof.
 intros k w x e env' K0 K HK HA Le. apply ret_frame_tau; [exact HK|reflexivity|reflexivity| |].
 - intros j w' f0 f s0 s c1 L W HV HS E. rewrite next_KHead_cons in E. injection E as <-.
   exists (Cfg (Ret f0) (KApply [VExn x] :: K0) s0). split; [apply srun_refl|].
   destruct j as [|j]; [apply ObsT_0|]. apply ObsT_running.
   + reflexivity.
   + unfold JitKRefBase.JitKRefBase.nonterm. rewrite (sval_next env' (EVar e) (VExn x) _ _ Le). exact I.
   + intros y. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|reflexivity|reflexivity|lia|exact W|eapply SRel_down; [|exact HS]; lia].
   + intros c2 E2. rewrite (sval_next env' (EVar e) (VExn x) _ _ Le) in E2. injection E2 as <-.
     exists (Cfg (Ret f0) (KApply [VExn x] :: K0) s0). split; [apply srun_refl|].
     apply (ObsT_swap j w' (Cfg (Ret f0) (KApply [VExn x] :: K0) s0) (Cfg (Ret f0) (KApply [VExn x] :: K0) s0)
             (Cfg (Ret (VExn x)) (KArgs f [] [] env' :: K) s) (Cfg (Ret f) (KApply [VExn x] :: K) s)).
     * split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
       exists (KApply [VExn x]), (KApply [VExn x]), K0. repeat split.
     * split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]].
       exists (KArgs f [] [] env'), (KApply [VExn x]), K. repeat split.
     * apply (HA (S (S j)) w' f0 f L W HV j w'); [lia|eapply wext_self; exact HS| |eapply SRel_down; [|exact HS]; lia].
       constructor; [apply VRel_exn|constructor].
   + intros q kk r E2. rewrite (sval_next env' (EVar e) (VExn x) _ _ Le) in E2. discriminate.
 - intros v s. eexists. apply next_KHead_cons.
Qed.

(* The handler phase: the target makes the eta closure (a cell only it has), applies it to the
   exception and evaluates the handler expression where the source evaluates its own. *)
Lemma trap_eta_handler : forall j w h0 rho0 e h rho K0 K x s0 s,
 KRel j w K0 K -> AppAll j w K0 K -> SRel j w s0 s ->
 (forall i w' l, (i <= j)%nat -> wext w w' -> ERel i w' rho0 h0 ((e, VExn x) :: (id_key, VVec l) :: rho) h) ->
 ObsT j w (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0)
          (Cfg (Eval rho (ELam e (EApp h [EVar e]))) (KApply [VExn x] :: K) s).
Proof.
 intros j w h0 rho0 e h rho K0 K x s0 s HK HA HS Hh.
 assert (Ww : wext w w) by (eapply wext_self; exact HS).
 assert (HS1 : SRel j w s0 (with_cell s)) by (apply SRel_with_cell_r; exact HS).
 assert (HKA : KRel j w (KApply [VExn x] :: K0) (KHead [EVar e] ((e, VExn x) :: tagged_env rho s) :: K)).
 { apply KRel_apply_head; [exact HK|exact HA|]. cbn [lookup]. rewrite text_eqb_refl. reflexivity. }
 destruct j as [|j1]; [apply ObsT_0|]. apply ObsT_running.
 - reflexivity.
 - unfold JitKRefBase.JitKRefBase.nonterm. rewrite next_lam. exact I.
 - intros y. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|reflexivity|reflexivity|lia|exact Ww|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite next_lam in E1. injection E1 as <-.
   exists (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0). split; [apply srun_refl|].
   destruct j1 as [|j2]; [apply ObsT_0|]. apply ObsT_running.
   + reflexivity.
   + unfold JitKRefBase.JitKRefBase.nonterm. rewrite next_ret_lam_exn. exact I.
   + intros y. cbn [kont mem]. eapply KRel_throw_frame; [exact HK|reflexivity|reflexivity|lia|exact Ww|eapply SRel_down; [|exact HS1]; lia].
   + intros c2 E2. rewrite next_ret_lam_exn in E2. injection E2 as <-.
     exists (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0). split; [apply srun_refl|].
     destruct j2 as [|j3]; [apply ObsT_0|]. apply ObsT_running.
     * reflexivity.
     * unfold JitKRefBase.JitKRefBase.nonterm. rewrite next_app. exact I.
     * intros y. cbn [kont mem]. eapply ObsT_anti; [eapply srun_tau; [apply throw_frame_next; reflexivity|apply srun_refl]|].
       apply KRel_throw; [eapply KRel_down; [|exact HK]; lia|eapply SRel_down; [|exact HS1]; lia].
     * intros c3 E3. rewrite next_app in E3. injection E3 as <-.
       exists (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0). split; [apply srun_refl|].
       eapply ERel_apply; [apply (Hh j3 w (List.length (heap s))); [lia|exact Ww]|apply le_n|exact Ww| |].
       -- eapply KRel_down; [|exact HKA]; lia.
       -- eapply SRel_down; [|exact HS1]; lia.
     * intros q kk r E3. rewrite next_app in E3. discriminate.
   + intros q kk r E2. rewrite next_ret_lam_exn in E2. discriminate.
 - intros q kk r E1. rewrite next_lam in E1. discriminate.
Qed.

Theorem KRel_trap_eta : forall k w h0 rho0 e h rho K0 K, KRel k w K0 K -> AppAll k w K0 K ->
 (forall j w' l x, (j <= k)%nat -> wext w w' -> ERel j w' rho0 h0 ((e, VExn x) :: (id_key, VVec l) :: rho) h) ->
 KRel k w (KTrap h0 rho0 :: K0) (KTrap (ELam e (EApp h [EVar e])) rho :: K).
Proof.
 intros k w h0 rho0 e h rho K0 K HK HA Hh.
 assert (Th : forall j w' x s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s ->
   ObsT j w' (Cfg (Throw x) (KTrap h0 rho0 :: K0) s0) (Cfg (Throw x) (KTrap (ELam e (EApp h [EVar e])) rho :: K) s)).
 { intros j w' x s0 s L W HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_step.
   - unfold JitKRefBase.JitKRefBase.nonterm. rewrite next_KTrap_throw. exact I.
   - intros l c1 St. destruct (step_r_cases _ _ _ St) as [[E ->]|[(q & kk & r & E & _)|(r & y & Rc & _)]].
     + rewrite next_KTrap_throw in E. injection E as <-.
       apply (ObsT_anti_io _ _ [] _ (Cfg (Eval rho0 h0) (KApply [VExn x] :: K0) s0)).
       * eapply srun_tau; [apply next_KTrap_throw|apply srun_refl].
       * apply trap_eta_handler.
         -- eapply KRel_mono; [|exact W|exact HK]; lia.
         -- eapply AppAll_mono; [|exact W|exact HA]; lia.
         -- eapply SRel_down; [|exact HS]; lia.
         -- intros i w'' l' Li W''. apply Hh; [lia|eapply wext_trans; eauto].
     + rewrite next_KTrap_throw in E. discriminate.
     + cbn in Rc. discriminate. }
 apply KRel_iff. intros j L w' W. split; [|intros x s0 s HS; apply Th; assumption].
 intros v0 v s0 s HV HS. destruct j as [|j]; [apply ObsT_0|]. apply ObsT_running.
 - reflexivity.
 - unfold JitKRefBase.JitKRefBase.nonterm. rewrite next_KTrap_ret. exact I.
 - intros x. cbn [kont mem]. apply Th; [lia|exact W|eapply SRel_down; [|exact HS]; lia].
 - intros c1 E. rewrite next_KTrap_ret in E. injection E as <-.
   eexists; split; [eapply srun_tau; [apply next_KTrap_ret|apply srun_refl]|]. eapply ret_at; eauto.
 - intros q kk r E. rewrite next_KTrap_ret in E. discriminate.
Qed.

Theorem trap_sugar : trap_sugar_statement.
Proof.
 intros g a0 a h0 h e Dw Ne Nid Ha Hh k w rho0 rho W HE.
 apply (ERel_push k w rho0 (ETrap a0 h0) rho (ETrap a (ELam e (EApp h [EVar e]))) rho0 a0 rho a
   (fun K0 => KTrap h0 rho0 :: K0) (fun K => KTrap (ELam e (EApp h [EVar e])) rho :: K)).
 - intros K0 s0. reflexivity.
 - intros K s. reflexivity.
 - intros j w' K0 K Lj W' HK. apply KRel_trap_eta; [exact HK|apply appall; [exact Dw|exact HK]|].
   intros i w'' l x Li W''. apply Hh; [exact (proj2 W'')|].
   apply EnvRel_skip_tgt; [|exact Ne]. apply EnvRel_skip_tgt; [|exact Nid].
   eapply EnvRel_mono; [|eapply wext_trans; [exact W'|exact W'']|exact HE]; lia.
 - intros j w' Lj W'. apply Ha; [exact (proj2 W')|eapply EnvRel_mono; [|exact W'|exact HE]; lia].
Qed.

(* ======================= the checkers ======================= *)
(* Congruence: the same construct on both sides, the parts checked by rec. A nested defun is not
   checked (lower.shen rejects it). *)
Definition chk_cong (rec : Chk) (g : list name) (e0 e : expr) : bool :=
 lit_eqb e0 e ||
 match e0, e with
 | EVar x, EVar y => text_eqb x y && bound g x
 | ELet x a0 b0, ELet y a b => text_eqb x y && rec g a0 a && rec (x :: g) b0 b
 | EIf c0 a0 b0, EIf c a b => rec g c0 c && rec g a0 a && rec g b0 b
 | EAnd a0 b0, EAnd a b => rec g a0 a && rec g b0 b
 | EOr a0 b0, EOr a b => rec g a0 a && rec g b0 b
 | ECond cl0, ECond cl => all2 (fun p0 p => rec g (fst p0) (fst p) && rec g (snd p0) (snd p)) cl0 cl
 | EType a0, EType a => rec g a0 a
 | ETrap a0 h0, ETrap a h => rec g a0 a && rec g h0 h
 | ELam x b0, ELam y b => text_eqb x y && rec (x :: g) b0 b
 | EFreeze b0, EFreeze b => rec g b0 b
 | ECall f as0, ECall f' as1 => text_eqb f f' && all2 (rec g) as0 as1
 | EApp h0 as0, EApp h as1 => rec g h0 h && all2 (rec g) as0 as1
 | _, _ => false end.

(* cond (norm-cond): the literal true ends the chain; any other clause is an if. *)
Definition chk_cond (rec : Chk) (g : list name) (e0 e : expr) : bool :=
 match e0 with
 | ECond ((c0, b0) :: rest0) =>
   (is_true_lit c0 && rec g b0 e) ||
   match e with EIf c b r => rec g c0 c && rec g b0 b && rec g (ECond rest0) r | _ => false end
 | _ => false end.

(* D holds the kernel's protect and thaw, read off D itself. *)
Definition has_protect : bool := match lookup protect_name D with
 | Some (FUser [p] (EVar q)) => text_eqb p q | _ => false end.
Definition has_thaw : bool := match lookup thaw_name D with
 | Some (FUser [p] (EApp (EVar q) [])) => text_eqb p q | _ => false end.

(* sugar: type, protect, lambda application. fn and curried dynamic application: no rule. *)
Definition chk_sugar (rec : Chk) (g : list name) (e0 e : expr) : bool :=
 match e0 with
 | EType a0 => rec g a0 e
 | ECall f [a0] => text_eqb f protect_name && has_protect && rec g a0 e
 | EApp (ELam x b0) [a0] => negb (bound g id_key) &&
     match e with ELet y a b => text_eqb x y && rec g a0 a && rec (x :: g) b0 b | _ => false end
 | _ => false end.

(* thaw sugar: (thaw X) is [apply X]. *)
Definition chk_thaw (rec : Chk) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | ECall f [a0], EApp a [] => text_eqb f thaw_name && has_thaw && rec g a0 a
 | _, _ => false end.

(* trap sugar: a handler that is not a lambda is applied to the exception through a fresh name. *)
Definition chk_trap (rec : Chk) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | ETrap a0 h0, ETrap a (ELam x (EApp h [EVar y])) =>
   text_eqb x y && negb (bound g x) && negb (bound g id_key) && rec g a0 a && rec g h0 h
 | _, _ => false end.

(* The four families and congruence, by fuel. *)
Fixpoint chk_front (n : nat) (g : list name) (e0 e : expr) {struct n} : bool :=
 match n with
 | O => false
 | S n' => chk_cong (chk_front n') g e0 e || chk_cond (chk_front n') g e0 e || chk_sugar (chk_front n') g e0 e ||
           chk_thaw (chk_front n') g e0 e || chk_trap (chk_front n') g e0 e end.

Definition RecSound (rec : Chk) : Prop := forall g a b, rec g a b = true -> KRef g a b.

Lemma has_protect_In : has_protect = true -> exists p, In (protect_name, FUser [p] (EVar p)) D.
Proof.
 unfold has_protect. destruct (lookup protect_name D) as [[pr|ps b]|] eqn:L; intro H; try discriminate.
 destruct ps as [|p [|p' ps]]; try discriminate.
 destruct b as [| | | | |q| | | | | | | | | | | |]; try discriminate.
 apply text_eqb_eq in H. subst. eexists. apply lookup_In_gen. exact L.
Qed.

Lemma has_thaw_In : has_thaw = true -> exists p, In (thaw_name, FUser [p] (EApp (EVar p) [])) D.
Proof.
 unfold has_thaw. destruct (lookup thaw_name D) as [[pr|ps b]|] eqn:L; intro H; try discriminate.
 destruct ps as [|p [|p' ps]]; try discriminate.
 destruct b as [| | | | | | | | | | | | | | | |h l|]; try discriminate.
 destruct h as [| | | | |q| | | | | | | | | | | |]; try discriminate.
 destruct l as [|a l]; try discriminate.
 apply text_eqb_eq in H. subst. eexists. apply lookup_In_gen. exact L.
Qed.

(* ---------- each family's checker, sound for any sound rec ---------- *)
Theorem chk_cond_sound : forall rec, RecSound rec -> forall g e0 e, chk_cond rec g e0 e = true -> KRef g e0 e.
Proof.
 intros rec Hr g e0 e H. unfold chk_cond in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a h|b|a|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct cl as [|[c0 b0] rest0]; cbv beta iota in H; try discriminate.
 apply orb_true_iff in H as [H|H].
 - apply andb_true_iff in H as [Ht Hb]. apply is_true_lit_eq in Ht. subst c0.
   apply cond_true. apply Hr. exact Hb.
 - destruct e; cbv beta iota in H; try discriminate. apply andb_true_iff in H as [H Hr3]. apply andb_true_iff in H as [Hr1 Hr2].
   apply cond_if; apply Hr; assumption.
Qed.

Theorem chk_sugar_sound : forall rec, RecSound rec -> forall g e0 e, chk_sugar rec g e0 e = true -> KRef g e0 e.
Proof.
 intros rec Hr g e0 e H. unfold chk_sugar in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a h|b|a|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 - (* type *)
   apply sugar_type. apply Hr. exact H.
 - (* lambda application *)
   destruct h as [n|t|s|b| |x|x b0|x a b|c a b|a b|a b|cl|a h|b|a|f ps b|h l0|f l0]; cbv beta iota in H; try discriminate.
   destruct l as [|a0 [|a1 l]]; cbv beta iota in H; try discriminate.
   apply andb_true_iff in H as [Nid H]. apply negb_true_iff in Nid.
   destruct e as [n|t|s|bb| |y|y bd|y a b|c a b|a b|a b|cl|a h|bd|a|f ps bd|h l0|f l0]; cbv beta iota in H; try discriminate.
   apply andb_true_iff in H as [H Hb]. apply andb_true_iff in H as [Hx Ha].
   apply text_eqb_eq in Hx. subst.
   apply sugar_lamapp; [apply bound_false; exact Nid|apply Hr; exact Ha|apply Hr; exact Hb].
 - (* protect *)
   destruct l as [|a0 [|a1 l]]; cbv beta iota in H; try discriminate.
   apply andb_true_iff in H as [H Ha]. apply andb_true_iff in H as [Hf Hp].
   apply text_eqb_eq in Hf. subst. destruct (has_protect_In Hp) as [p I].
   eapply sugar_protect; [exists p; exact I|apply Hr; exact Ha].
Qed.

Theorem chk_thaw_sound : D_wf -> forall rec, RecSound rec -> forall g e0 e, chk_thaw rec g e0 e = true -> KRef g e0 e.
Proof.
 intros Dw rec Hr g e0 e H. unfold chk_thaw in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a h|b|a|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct l as [|a0 [|a1 l]]; cbv beta iota in H; try discriminate.
 destruct e as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a h|b|a|f' ps b|h l|f' l]; cbv beta iota in H; try discriminate.
 destruct l as [|a1 l]; cbv beta iota in H; try discriminate.
 apply andb_true_iff in H as [H Ha]. apply andb_true_iff in H as [Hf Ht].
 apply text_eqb_eq in Hf. subst. destruct (has_thaw_In Ht) as [p I].
 eapply thaw_sugar; [exact Dw|exists p; exact I|apply Hr; exact Ha].
Qed.

Theorem chk_trap_sound : D_wf -> forall rec, RecSound rec -> forall g e0 e, chk_trap rec g e0 e = true -> KRef g e0 e.
Proof.
 intros Dw rec Hr g e0 e H. unfold chk_trap in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a0 h0|b|a|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct e as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|a hd|b|a|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct hd as [n|t|s|b| |x'|x bd|x' a' b|c a' b|a' b|a' b|cl|a' h|b|a'|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct bd as [n|t|s|b| |x'|x' b|x' a' b|c a' b|a' b|a' b|cl|a' h'|b|a'|f ps b|h l|f l]; cbv beta iota in H; try discriminate.
 destruct l as [|v l]; cbv beta iota in H; try discriminate.
 destruct v as [n|t|s|b| |y|x' b|x' a' b|c a' b|a' b|a' b|cl|a' h'|b|a'|f ps b|h' l'|f l']; cbv beta iota in H; try discriminate.
 destruct l as [|v' l]; cbv beta iota in H; try discriminate.
 apply andb_true_iff in H as [H Hh]. apply andb_true_iff in H as [H Ha].
 apply andb_true_iff in H as [H Nid]. apply andb_true_iff in H as [Hx Nx].
 apply text_eqb_eq in Hx. subst. apply negb_true_iff in Nid, Nx.
 apply trap_sugar; [exact Dw|apply bound_false; exact Nx|apply bound_false; exact Nid|apply Hr; exact Ha|apply Hr; exact Hh].
Qed.

(* ---------- congruence, and the combined checker, under the compatibility statements ---------- *)
Section FromCompat.
Hypothesis Dw : D_wf.
Hypothesis c_lit : compat_lit_statement.
Hypothesis c_var : compat_var_statement.
Hypothesis c_let : compat_let_statement.
Hypothesis c_if : compat_if_statement.
Hypothesis c_and : compat_and_statement.
Hypothesis c_or : compat_or_statement.
Hypothesis c_cond : compat_cond_statement.
Hypothesis c_type : compat_type_statement.
Hypothesis c_trap : compat_trap_statement.
Hypothesis c_lambda : compat_lambda_statement.
Hypothesis c_freeze : compat_freeze_statement.
Hypothesis c_call : compat_call_statement.
Hypothesis c_app : compat_app_statement.

Theorem chk_cong_sound_h : forall rec, RecSound rec -> forall g e0 e, chk_cong rec g e0 e = true -> KRef g e0 e.
Proof.
 intros rec Hr g e0 e H. unfold chk_cong in H. apply orb_true_iff in H as [H|H].
 { apply lit_eqb_spec in H as [<- [v Hv]]. eapply c_lit; exact Hv. }
 destruct e0; destruct e; cbv beta iota in H; try discriminate;
 repeat match goal with Hb : (_ && _)%bool = true |- _ => apply andb_true_iff in Hb as [? ?] end.
 - (* var *) match goal with Hx : text_eqb _ _ = true |- _ => apply text_eqb_eq in Hx; subst end.
   apply c_var. apply bound_true. assumption.
 - (* lambda *) match goal with Hx : text_eqb _ _ = true |- _ => apply text_eqb_eq in Hx; subst end.
   apply c_lambda. apply Hr. assumption.
 - (* let *) match goal with Hx : text_eqb _ _ = true |- _ => apply text_eqb_eq in Hx; subst end.
   apply c_let; apply Hr; assumption.
 - (* if *) apply c_if; apply Hr; assumption.
 - (* and *) apply c_and; apply Hr; assumption.
 - (* or *) apply c_or; apply Hr; assumption.
 - (* cond *) apply c_cond. eapply all2_Forall2; [|eassumption]. intros p0 p Hp.
   apply andb_true_iff in Hp as [H1 H2]. split; apply Hr; assumption.
 - (* trap *) apply c_trap; [exact Dw|apply Hr; assumption|apply Hr; assumption].
 - (* freeze *) apply c_freeze. apply Hr. assumption.
 - (* type *) apply c_type. apply Hr. assumption.
 - (* app *) apply c_app; [exact Dw|apply Hr; assumption|]. eapply all2_Forall2; [|eassumption]. intros a b; apply Hr.
 - (* call *) match goal with Hx : text_eqb _ _ = true |- _ => apply text_eqb_eq in Hx; subst end.
   apply c_call; [exact Dw|]. eapply all2_Forall2; [|eassumption]. intros a b; apply Hr.
Qed.

Theorem chk_front_sound_h : forall n g e0 e, chk_front n g e0 e = true -> KRef g e0 e.
Proof.
 induction n as [|n IH]; intros g e0 e H; [discriminate|]. cbn [chk_front] in H.
 apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H];
   [apply orb_true_iff in H as [H|H]|]|]|].
 - exact (chk_cong_sound_h _ IH g e0 e H).
 - exact (chk_cond_sound _ IH g e0 e H).
 - exact (chk_sugar_sound _ IH g e0 e H).
 - exact (chk_thaw_sound Dw _ IH g e0 e H).
 - exact (chk_trap_sound Dw _ IH g e0 e H).
Qed.
End FromCompat.

(* Instantiated: no hypothesis remains but D_wf. *)
Theorem chk_cong_sound : D_wf -> forall rec, RecSound rec -> forall g e0 e, chk_cong rec g e0 e = true -> KRef g e0 e.
Proof.
 intros Dw. apply chk_cong_sound_h; [exact Dw|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_var sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_let sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_if sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_and sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_or sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_cond sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_type sealed D)|
   exact (JitKRefFund.JitKRefFund.compat_trap sealed D)|exact (JitKRefCompatClo.JitKRefCompatClo.compat_lambda sealed D)|
   exact (JitKRefCompatClo.JitKRefCompatClo.compat_freeze sealed D)|exact (JitKRefFund.JitKRefFund.compat_call sealed D)|
   exact (JitKRefFund.JitKRefFund.compat_app sealed D)].
Qed.

Theorem chk_front_sound : D_wf -> forall n g e0 e, chk_front n g e0 e = true -> KRef g e0 e.
Proof.
 intros Dw. apply chk_front_sound_h; [exact Dw|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_var sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_let sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_if sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_and sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_or sealed D)|
   exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_cond sealed D)|exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_type sealed D)|
   exact (JitKRefFund.JitKRefFund.compat_trap sealed D)|exact (JitKRefCompatClo.JitKRefCompatClo.compat_lambda sealed D)|
   exact (JitKRefCompatClo.JitKRefCompatClo.compat_freeze sealed D)|exact (JitKRefFund.JitKRefFund.compat_call sealed D)|
   exact (JitKRefFund.JitKRefFund.compat_app sealed D)].
Qed.
End Equiv.

(* ======================= pinned behaviour (tests, not evidence of anything general) ======================= *)
Definition nm (s : string) : name := of_string s.
Definition Dk : list (name * fundef) :=
 [(protect_name, FUser [nm "V"] (EVar (nm "V"))); (thaw_name, FUser [nm "V"] (EApp (EVar (nm "V")) []))].

(* (cond (C B1) (true B2)) is (if C B1 B2). *)
Example cond_chain_accepted :
 chk_front Dk 10 [nm "C"] (ECond [(EVar (nm "C"), ENum (NInt 1)); (EBool true, ENum (NInt 2))])
   (EIf (EVar (nm "C")) (ENum (NInt 1)) (ENum (NInt 2))) = true.
Proof. vm_compute. reflexivity. Qed.
(* The branches swapped: rejected. *)
Example cond_chain_swapped_rejected :
 chk_front Dk 10 [nm "C"] (ECond [(EVar (nm "C"), ENum (NInt 1)); (EBool true, ENum (NInt 2))])
   (EIf (EVar (nm "C")) (ENum (NInt 2)) (ENum (NInt 1))) = false.
Proof. vm_compute. reflexivity. Qed.
(* A chain with no true clause ends in the raise (ECond []). *)
Example cond_raise_accepted :
 chk_front Dk 10 [nm "C"] (ECond [(EVar (nm "C"), ENum (NInt 1))]) (EIf (EVar (nm "C")) (ENum (NInt 1)) (ECond [])) = true.
Proof. vm_compute. reflexivity. Qed.
(* (protect (type X t)) is X, with the kernel's protect in D; without it, rejected. *)
Example protect_type_accepted :
 chk_front Dk 10 [nm "X"] (ECall protect_name [EType (EVar (nm "X"))]) (EVar (nm "X")) = true.
Proof. vm_compute. reflexivity. Qed.
Example protect_without_D_rejected :
 chk_front [] 10 [nm "X"] (ECall protect_name [EVar (nm "X")]) (EVar (nm "X")) = false.
Proof. vm_compute. reflexivity. Qed.
(* (thaw X) is [apply X]. *)
Example thaw_accepted : chk_front Dk 10 [nm "X"] (ECall thaw_name [EVar (nm "X")]) (EApp (EVar (nm "X")) []) = true.
Proof. vm_compute. reflexivity. Qed.
(* ((lambda Y Y) 1) is (let Y 1 Y). *)
Example lamapp_accepted :
 chk_front Dk 10 [] (EApp (ELam (nm "Y") (EVar (nm "Y"))) [ENum (NInt 1)]) (ELet (nm "Y") (ENum (NInt 1)) (EVar (nm "Y"))) = true.
Proof. vm_compute. reflexivity. Qed.
(* Two arguments: the source evaluates the second before the body. No rule. *)
Example lamapp_two_rejected :
 chk_front Dk 10 [nm "M"] (EApp (ELam (nm "Y") (EVar (nm "Y"))) [ENum (NInt 1); EVar (nm "M")])
   (EApp (ELet (nm "Y") (ENum (NInt 1)) (EVar (nm "Y"))) [EVar (nm "M")]) = false.
Proof. vm_compute. reflexivity. Qed.
(* Curried dynamic application: no rule. *)
Example curried_rejected :
 chk_front Dk 10 [nm "F"; nm "A"; nm "B"] (EApp (EVar (nm "F")) [EVar (nm "A"); EVar (nm "B")])
   (EApp (EApp (EVar (nm "F")) [EVar (nm "A")]) [EVar (nm "B")]) = false.
Proof. vm_compute. reflexivity. Qed.
(* eval-kl to a call of shen-jit.eval-kl: no rule. *)
Example evalkl_rejected :
 chk_front Dk 10 [nm "X"] (ECall (nm "eval-kl") [EVar (nm "X")]) (ECall (nm "shen-jit.eval-kl") [EVar (nm "X")]) = false.
Proof. vm_compute. reflexivity. Qed.
(* ((fn F) X) to (F X): no rule. *)
Example fn_rejected :
 chk_front Dk 10 [nm "X"] (EApp (ECall (nm "fn") [ESym (nm "f")]) [EVar (nm "X")]) (ECall (nm "f") [EVar (nm "X")]) = false.
Proof. vm_compute. reflexivity. Qed.
(* (trap-error X H) with H a variable: the handler is applied through a fresh name. *)
Example trap_eta_accepted :
 chk_front Dk 10 [nm "X"; nm "H"] (ETrap (EVar (nm "X")) (EVar (nm "H")))
   (ETrap (EVar (nm "X")) (ELam (nm "stage0.lower.exception1") (EApp (EVar (nm "H")) [EVar (nm "stage0.lower.exception1")]))) = true.
Proof. vm_compute. reflexivity. Qed.
(* The fresh name is in scope: rejected. *)
Example trap_eta_captured_rejected :
 chk_front Dk 10 [nm "X"; nm "H"] (ETrap (EVar (nm "X")) (EVar (nm "H")))
   (ETrap (EVar (nm "X")) (ELam (nm "H") (EApp (EVar (nm "H")) [EVar (nm "H")]))) = false.
Proof. vm_compute. reflexivity. Qed.
(* (trap-error X (lambda E H)) is congruence. *)
Example trap_lambda_accepted :
 chk_front Dk 10 [nm "X"] (ETrap (EVar (nm "X")) (ELam (nm "E") (EVar (nm "E"))))
   (ETrap (EVar (nm "X")) (ELam (nm "E") (EVar (nm "E")))) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================= the real table (a test harness; NOT evidence of anything general) ======================= *)
(* Each decoded stage 0 row (JitFrontD.decode_row: the source body, the erasure of its .norm
   witness) checked by chk_front in the row's own D (JitFrontD.D_of), with fuel the two sizes. The
   source is the definition's form, not share's output, so a definition share rewrote is expected to
   be rejected here. Run by vm_compute on the decoded table; what the run gives is a test result. *)
Definition front_row (rows : list JitFrontD.JitFrontD.row) (r : JitFrontD.JitFrontD.row) : bool :=
 match JitFrontD.JitFrontD.D_of rows (JitFrontD.JitFrontD.r_name r) with
 | Some D => chk_front D (S (JitFrontD.JitFrontD.dsize (JitFrontD.JitFrontD.r_src r) +
                            JitFrontD.JitFrontD.dsize (JitFrontD.JitFrontD.r_low r)))
               (JitFrontD.JitFrontD.r_params r) (JitFrontD.JitFrontD.r_src r) (JitFrontD.JitFrontD.r_low r)
 | None => false end.
Definition front_report (rows : list JitFrontD.JitFrontD.row) : nat * nat * list string :=
 let acc := filter (front_row rows) rows in
 (List.length rows, List.length acc, map (fun r => JitNormStage0.JitNormStage0.show (JitFrontD.JitFrontD.r_name r)) acc).
End JitFrontSugar.
