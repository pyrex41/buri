(* Shen/JIT Phase 2, front track, r1-f-copy-fold-apply: norm's constant folding (cons, + and -),
   dynamic-application uncurrying, and freeze and lambda copying, against KRef.

   What lower.shen does (934cfa5, src/lowerer/lower.shen, `shen-jit.lower.prim`, `norm-apply`,
   `let-frozen`, `frozen-late`, `let-lambda`, `inline-frozen`), and what this file proves of each:

   - fold-cons: (cons [const A] [const B]) becomes [const (A . B)] for a proper B. The erasure of a
     pair constant IS the cons chain (JitNorm.erase_const), so at KLambda the folded witness and
     the source are the same expression: fold_cons_erase proves erase of the folded node equals
     erase of the unfolded [prim cons ...] node, for every scope and every pair, and cf_chk accepts
     it by congruence (compat_call). No store fact is used (as JitFrontD's D_cons_prim notes).
   - fold-arith: (+ [const A] [const B]) and (- ...) become [const (A +/- B)] for small integers.
     At KLambda the source (ECall + [a; b]) and the target ENum (NInt c) differ. The rule `cfold`
     evaluates the source side (integer literals, nested + and -), and accepts only when
     (+, FPrim PAdd) (resp. (-, FPrim PSub)) is IN D and every intermediate result is inside the
     fixnum range of jit_rules (otherwise + raises, KLPort.rule_arith_r). Soundness is source
     anti-reduction to the returned value (cfold_run: the source steps silently to Ret c in every
     store meeting D; ERel_src_ret: then it is related to the literal). The D fact is the rule's
     own premise, checked by the checker (d_has), never assumed: JitFrontD's interface item 2 says
     a D built by D_of never holds + or - (they are not in stage 0's sealed list), so on real D
     stores fold-arith is accepted only once that item is settled.
   - dynamic application: norm-apply turns (F A B) into ((F A) B). Erased, the source is
     EApp F [A; B] and the witness EApp (EApp F [A]) [B]. This is NOT a KRef refinement:
     uncurry_not_kref proves, with no premise, that for F bound to a partial application
     (VPartial g [] for a g of arity 2, a value VRel relates to itself) the source returns while
     the target raises XArity (jit_rules has arity errors, so a partial call of one argument
     raises), which no source run can match. So no sound checker accepts this rewrite against
     KRef as it stands; cf_chk does not. (A second, independent failure for a non-atomic B is the
     evaluation order: the source evaluates B before applying F to A, the witness after.) What it
     would take is a design decision outside this file: either erase maps an apply chain back to
     the multi-argument EApp of the source (the emitter's apply-all already evaluates every
     argument first when they are variables or constants), or KRef's environments exclude
     partial applications. Either changes a reviewed statement and is Reuben's call.
   - freeze copying (let-frozen copy, frozen-late hoist, inline-frozen) and lambda copying
     (let-lambda): NOT proved here. Each removes a closure the source makes and copies its body
     to its use sites, so the use-site check needs a fact about the source environment (X is
     bound to the frozen/lambda closure of E over the let's environment, and no binder between
     rebinds a free name of E) that KRef's environment relation does not carry; source
     anti-reduction to an intermediate SOURCE TERM cannot express it, because the intermediate
     is a configuration whose environment holds a closure. Proving them needs a new logical
     relation lemma (a source-only known-closure environment, threaded through the body) that
     is not written. let-frozen copy also always involves shen.bind! (frozen-binds? gates it),
     whose bound-now rewrite is another family's. frozen-late's re-evaluated test may call
     shen-jit.pvar?, a port primitive with no source meaning (OB-JIT-PORT-PRIMS).

   The checker cf_chk (fuel, scope, source, witness) accepts: equal literals; a variable in scope;
   the same head constructor with the parts accepted (the scope extended under let, lambda);
   and fold-arith. It is proved sound first under Section hypotheses naming KRef's compat_*
   statements (cf_chk_sound_hyp), then instantiated with JitKRefCompatCtl, JitKRefCompatClo and
   JitKRefFund, so cf_chk_sound has D_wf as its only premise.

   Proved here (each in Audit_Jit, "Closed under the global context"): fold_cons_erase, cfold_run,
   ERel_src_ret, fold_arith_kref, cf_chk_sound_hyp, cf_chk_sound, uncurry_not_kref.
   Tests, not evidence of anything general: the Examples at the end.
   No axioms, nothing Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatCtl JitKRefCompatClo JitKRefCompatCall JitKRefFv JitKRefPrim JitKRefFund JitNorm.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontCopyFold.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel.
Module K := JitKRef.JitKRef.
Module KB := JitKRefBase.JitKRefBase.
Module KG := JitKRefGround.JitKRefGround.
Module N := JitNorm.JitNorm.

(* ======================= fold-cons: the erasure undoes it ======================= *)
Theorem fold_cons_erase : forall sc a d,
 N.erase sc (N.NConst (VCons a d)) = N.erase sc (N.NPrim N.cons_name [N.NConst a; N.NConst d]).
Proof.
 intros sc a d. cbn [N.erase N.erase_const].
 destruct (N.erase_const a) as [ea|]; destruct (N.erase_const d) as [ed|]; reflexivity.
Qed.

(* ======================= the checker ======================= *)
Definition plus_name : name := of_string "+".
Definition minus_name : name := of_string "-".
Definition is_add (d : fundef) : bool := match d with FPrim PAdd => true | _ => false end.
Definition is_sub (d : fundef) : bool := match d with FPrim PSub => true | _ => false end.
Definition d_has (D : list (name * fundef)) (f : name) (t : fundef -> bool) : bool :=
 existsb (fun q => text_eqb (fst q) f && t (snd q)) D.

(* jit_rules' fixnum range (KLPort.in_range at JitProfile.jit_rules). *)
Definition fits (z : Z) : bool := (Z.leb JitBytecode.JitBytecode.fix_min z && Z.leb z JitBytecode.JitBytecode.fix_max)%bool.

(* The integer a source expression folds to: an integer literal, or + / - of two such, each
   intermediate in range, with the primitive's entry in D. *)
Fixpoint cfold (D : list (name * fundef)) (e : expr) : option Z := match e with
 | ENum (NInt z) => Some z
 | ECall f [a; b] =>
   match cfold D a, cfold D b with
   | Some x, Some y =>
     if (text_eqb f plus_name && d_has D plus_name is_add && fits (x + y))%bool then Some (x + y)%Z
     else if (text_eqb f minus_name && d_has D minus_name is_sub && fits (x - y))%bool then Some (x - y)%Z
     else None
   | _, _ => None end
 | _ => None end.

Fixpoint forall2b {A B} (f : A -> B -> bool) (l0 : list A) (l : list B) : bool := match l0, l with
 | [], [] => true
 | a :: l0, b :: l => f a b && forall2b f l0 l
 | _, _ => false end.

Definition num_eqb (a b : num) : bool := match a, b with
 | NInt x, NInt y => Z.eqb x y | NFloat x, NFloat y => N.eqb x y | _, _ => false end.

(* Equal literals. *)
Definition lit_eqb (a b : expr) : bool := match a, b with
 | ENum x, ENum y => num_eqb x y
 | EStr x, EStr y | ESym x, ESym y => text_eqb x y
 | EBool x, EBool y => Bool.eqb x y
 | ENil, ENil => true
 | _, _ => false end.

(* One node: the same head constructor, the parts by `rec`. No defun (lower.shen rejects a nested
   one). *)
Definition cf_same (rec : list name -> expr -> expr -> bool) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | EVar x, EVar y => text_eqb x y && bound g x
 | ELam x b0, ELam y b => text_eqb x y && rec (x :: g) b0 b
 | ELet x a0 b0, ELet y a b => text_eqb x y && rec g a0 a && rec (x :: g) b0 b
 | EIf c0 a0 b0, EIf c a b => rec g c0 c && rec g a0 a && rec g b0 b
 | EAnd a0 b0, EAnd a b | EOr a0 b0, EOr a b | ETrap a0 b0, ETrap a b => rec g a0 a && rec g b0 b
 | ECond cl0, ECond cl => forall2b (fun p0 p => rec g (fst p0) (fst p) && rec g (snd p0) (snd p)) cl0 cl
 | EFreeze b0, EFreeze b | EType b0, EType b => rec g b0 b
 | EApp h0 as0, EApp h as1 => rec g h0 h && forall2b (rec g) as0 as1
 | ECall f as0, ECall f' as1 => text_eqb f f' && forall2b (rec g) as0 as1
 | _, _ => lit_eqb e0 e end.

Fixpoint cf_chk (D : list (name * fundef)) (n : nat) (g : list name) (e0 e : expr) {struct n} : bool :=
 match n with
 | O => false
 | S n => match cfold D e0, e with
   | Some z, ENum (NInt z') => Z.eqb z z'
   | _, _ => false end || cf_same (cf_chk D n) g e0 e end.

(* ======================= syntactic lemmas ======================= *)
Lemma forall2b_sound : forall {A B} (f : A -> B -> bool) (Q : A -> B -> Prop),
 (forall a b, f a b = true -> Q a b) -> forall l0 l, forall2b f l0 l = true -> Forall2 Q l0 l.
Proof.
 intros A B f Q H l0. induction l0 as [|a l0 IH]; intros [|b l] E; cbn in E; try discriminate; [constructor|].
 apply andb_true_iff in E as [E1 E2]. constructor; [apply H; exact E1|apply IH; exact E2].
Qed.

Lemma lit_eqb_sound : forall a b, lit_eqb a b = true -> a = b /\ exists v, lit_val a = Some v.
Proof.
 intros [] [] H; cbn in H; try discriminate; try (apply text_eqb_eq in H; subst);
 try (split; [reflexivity|eexists; reflexivity]).
 - destruct n as [x|x], n0 as [y|y]; cbn in H; try discriminate.
   + apply Z.eqb_eq in H; subst; split; [reflexivity|eexists; reflexivity].
   + apply N.eqb_eq in H; subst; split; [reflexivity|eexists; reflexivity].
 - apply Bool.eqb_prop in H; subst; split; [reflexivity|eexists; reflexivity].
Qed.

Lemma d_has_in : forall D f t, d_has D f t = true -> exists d, In (f, d) D /\ t d = true.
Proof.
 intros D f t H. unfold d_has in H. apply existsb_exists in H as ([f' d] & I & E).
 cbn in E. apply andb_true_iff in E as [E1 E2]. apply text_eqb_eq in E1. subst f'. eauto.
Qed.

Lemma is_add_eq : forall d, is_add d = true -> d = FPrim PAdd.
Proof. intros [[] |] H; cbn in H; try discriminate; reflexivity. Qed.
Lemma is_sub_eq : forall d, is_sub d = true -> d = FPrim PSub.
Proof. intros [[] |] H; cbn in H; try discriminate; reflexivity. Qed.

(* ======================= fold-arith: the source runs to the folded value ======================= *)
Section Fold.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (K.srun sealed).
Notation StoreHas := (K.StoreHas D).
Notation VRel := (K.VRel sealed D).
Notation ERel := (K.ERel sealed D).
Notation KRef := (K.KRef sealed D).

Lemma in_range_fits : forall z, in_range R z = fits z.
Proof. intros z. reflexivity. Qed.

Lemma call_arith : forall f p iop x y K s, lookup f (gfuns s) = Some (FPrim p) ->
 prim_arity p = 2%nat -> (forall a, prim_rule_r R P p a s = rule_arith_r R P p iop a s) -> fits (iop x y) = true ->
 call_named_r R P f [VNum (NInt x); VNum (NInt y)] K s = MTau (Cfg (Ret (VNum (NInt (iop x y)))) K s).
Proof.
 intros f p iop x y K s L A Hp F. unfold call_named_r. rewrite L.
 assert (M : arity_mismatch R 2 (prim_arity p) = false) by (rewrite A; reflexivity).
 change (List.length [VNum (NInt x); VNum (NInt y)]) with 2%nat. rewrite M, A.
 change (Nat.ltb 2 2) with false. cbv iota.
 unfold prim_move_r. change (firstn 2 [VNum (NInt x); VNum (NInt y)]) with [VNum (NInt x); VNum (NInt y)].
 change (skipn 2 [VNum (NInt x); VNum (NInt y)]) with (@nil value).
 rewrite Hp. unfold rule_arith_r. rewrite in_range_fits, F. reflexivity.
Qed.

Lemma srun_call2 : forall f a b x y rho K s v,
 (forall K', srun (Cfg (Eval rho a) K' s) [] (Cfg (Ret (VNum (NInt x))) K' s)) ->
 (forall K', srun (Cfg (Eval rho b) K' s) [] (Cfg (Ret (VNum (NInt y))) K' s)) ->
 call_named_r R P f [VNum (NInt x); VNum (NInt y)] K s = MTau (Cfg (Ret v) K s) ->
 srun (Cfg (Eval rho (ECall f [a; b])) K s) [] (Cfg (Ret v) K s).
Proof.
 intros f a b x y rho K s v Ha Hb Hc.
 eapply KB.srun_tau; [reflexivity|].
 refine (KB.srun_trans sealed _ [] _ [] _ (Ha _) _).
 eapply KB.srun_tau; [apply KB.next_KCallArgs_cons|].
 refine (KB.srun_trans sealed _ [] _ [] _ (Hb _) _).
 eapply KB.srun_tau; [|apply KB.srun_refl]. exact Hc.
Qed.

Theorem cfold_run : forall e z, cfold D e = Some z -> forall rho K s, StoreHas s ->
 srun (Cfg (Eval rho e) K s) [] (Cfg (Ret (VNum (NInt z))) K s).
Proof.
 fix IH 1. intros e z H rho K s Hs. destruct e as [n | | | | | | | | | | | | | | | | |f args]; cbn [cfold] in H; try discriminate.
 - destruct n as [z'|]; [|discriminate]. injection H as <-.
   eapply KB.srun_tau; [reflexivity|apply KB.srun_refl].
 - destruct args as [|a [|b [|c rest]]]; try discriminate.
   destruct (cfold D a) as [x|] eqn:Ea; [|discriminate]. destruct (cfold D b) as [y|] eqn:Eb; [|discriminate].
   assert (Ha : forall K', srun (Cfg (Eval rho a) K' s) [] (Cfg (Ret (VNum (NInt x))) K' s))
     by (intros K'; exact (IH a x Ea rho K' s Hs)).
   assert (Hb : forall K', srun (Cfg (Eval rho b) K' s) [] (Cfg (Ret (VNum (NInt y))) K' s))
     by (intros K'; exact (IH b y Eb rho K' s Hs)).
   destruct (text_eqb f plus_name && d_has D plus_name is_add && fits (x + y))%bool eqn:E1.
   + injection H as <-. apply andb_true_iff in E1 as [E1 F]. apply andb_true_iff in E1 as [Ef Ed].
     apply text_eqb_eq in Ef. subst f. destruct (d_has_in _ _ _ Ed) as (d & I & Td). apply is_add_eq in Td. subst d.
     apply srun_call2 with (x := x) (y := y); [exact Ha|exact Hb|].
     apply (call_arith plus_name PAdd Z.add); [exact (Hs _ _ I)|reflexivity|intros; reflexivity|exact F].
   + destruct (text_eqb f minus_name && d_has D minus_name is_sub && fits (x - y))%bool eqn:E2; [|discriminate].
     injection H as <-. apply andb_true_iff in E2 as [E2 F]. apply andb_true_iff in E2 as [Ef Ed].
     apply text_eqb_eq in Ef. subst f. destruct (d_has_in _ _ _ Ed) as (d & I & Td). apply is_sub_eq in Td. subst d.
     apply srun_call2 with (x := x) (y := y); [exact Ha|exact Hb|].
     apply (call_arith minus_name PSub Z.sub); [exact (Hs _ _ I)|reflexivity|intros; reflexivity|exact F].
Qed.

(* Source anti-reduction to a value: a source that steps silently to Ret v0, in every store
   meeting D and under every continuation, is related to a target that is a literal or a bound
   variable with a related value. *)
Theorem ERel_src_ret : forall k w rho0 e0 rho e v0 v,
 (forall K0 s0, StoreHas s0 -> srun (Cfg (Eval rho0 e0) K0 s0) [] (Cfg (Ret v0) K0 s0)) ->
 KB.sval rho e = Some v -> VRel k w v0 v -> ERel k w rho0 e0 rho e.
Proof.
 intros k w rho0 e0 rho e v0 v H0 Hv HV. apply (KB.ERel_iff sealed D). intros j L w' W K0 K HK s0 s HS.
 destruct j as [|j]; [apply KB.ObsT_0|]. apply KB.ObsT_running.
 - reflexivity.
 - unfold KB.nonterm. rewrite (KB.sval_next sealed rho e v K s Hv). exact I.
 - intros x. cbn [kont mem]. apply (KB.KRel_throw sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.SRel_down; [|exact HS]; lia].
 - intros c1 E1. rewrite (KB.sval_next sealed rho e v K s Hv) in E1. injection E1 as <-.
   exists (Cfg (Ret v0) K0 s0). split; [apply H0; destruct HS as (_ & Hs0 & _); exact Hs0|].
   apply (KB.KRel_ret sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.VRel_mono; [|exact W|exact HV]; lia|eapply KB.SRel_down; [|exact HS]; lia].
 - intros q kk r E1. rewrite (KB.sval_next sealed rho e v K s Hv) in E1. discriminate.
Qed.

Theorem fold_arith_kref : forall g e0 z, cfold D e0 = Some z -> KRef g e0 (ENum (NInt z)).
Proof.
 intros g e0 z H k w rho0 rho _ _. apply ERel_src_ret with (v0 := VNum (NInt z)) (v := VNum (NInt z)).
 - intros K0 s0 Hs. apply cfold_run; assumption.
 - reflexivity.
 - eapply JitKRefCompatCtl.JitKRefCompatCtl.VRel_lit with (e := ENum (NInt z)). reflexivity.
Qed.
End Fold.

(* ======================= soundness under the compat statements ======================= *)
Section Sound.
Variables (sealed : list name) (D : list (name * fundef)).
Notation KRef := (K.KRef sealed D).
Hypotheses
 (Hlit : K.compat_lit_statement sealed D) (Hvar : K.compat_var_statement sealed D)
 (Hlet : K.compat_let_statement sealed D) (Hif : K.compat_if_statement sealed D)
 (Hand : K.compat_and_statement sealed D) (Hor : K.compat_or_statement sealed D)
 (Hcond : K.compat_cond_statement sealed D) (Htype : K.compat_type_statement sealed D)
 (Htrap : K.compat_trap_statement sealed D) (Hlam : K.compat_lambda_statement sealed D)
 (Hfrz : K.compat_freeze_statement sealed D) (Hcall : K.compat_call_statement sealed D)
 (Happ : K.compat_app_statement sealed D) (Dw : K.D_wf sealed D).

Lemma cf_same_sound : forall (rec : list name -> expr -> expr -> bool),
 (forall g a b, rec g a b = true -> KRef g a b) ->
 forall g e0 e, cf_same rec g e0 e = true -> KRef g e0 e.
Proof.
 intros rec Hr g e0 e H.
 destruct e0; destruct e; cbn [cf_same] in H;
 repeat match goal with E : (_ && _)%bool = true |- _ => apply andb_true_iff in E as [? ?] end;
 repeat match goal with E : text_eqb _ _ = true |- _ => apply text_eqb_eq in E; subst end;
 first
 [ discriminate
 | apply lit_eqb_sound in H as [<- [v Hv]]; exact (Hlit g _ v Hv)
 | cbn [lit_eqb] in H; discriminate
 | exact (Hlit g ENil VNil eq_refl)
 | apply Hvar; apply JitKRefFv.JitKRefFv.bound_In; assumption
 | apply Hlam; apply Hr; assumption
 | apply Hlet; apply Hr; assumption
 | apply Hif; apply Hr; assumption
 | apply Hand; apply Hr; assumption
 | apply Hor; apply Hr; assumption
 | apply Htrap; [exact Dw|apply Hr; assumption|apply Hr; assumption]
 | apply Hfrz; apply Hr; assumption
 | apply Htype; apply Hr; assumption
 | apply Hcond; eapply forall2b_sound; [|exact H]; intros p0 p E; apply andb_true_iff in E as [E1 E2];
   split; apply Hr; assumption
 | apply Happ; [exact Dw|apply Hr; assumption|eapply forall2b_sound; [|eassumption]; exact (Hr g)]
 | apply Hcall; [exact Dw|eapply forall2b_sound; [|eassumption]; exact (Hr g)] ].
Qed.

Theorem cf_chk_sound_hyp : forall n g e0 e, cf_chk D n g e0 e = true -> KRef g e0 e.
Proof.
 induction n as [|n IH]; intros g e0 e H; cbn [cf_chk] in H; [discriminate|].
 apply orb_true_iff in H as [H|H].
 - destruct (cfold D e0) as [z|] eqn:Ez; [|discriminate]. destruct e as [[z'|] | | | | | | | | | | | | | | | | | ]; try discriminate.
   apply Z.eqb_eq in H. subst z'. apply fold_arith_kref. exact Ez.
 - eapply cf_same_sound; [exact IH|exact H].
Qed.
End Sound.

(* ======================= instantiated: D_wf is the only premise ======================= *)
Theorem cf_chk_sound : forall sealed D, K.D_wf sealed D ->
 forall n g e0 e, cf_chk D n g e0 e = true -> K.KRef sealed D g e0 e.
Proof.
 intros sealed D Dw. apply cf_chk_sound_hyp.
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_lit sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_var sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_let sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_if sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_and sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_or sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_cond sealed D).
 - exact (JitKRefCompatCtl.JitKRefCompatCtl.compat_type sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_trap sealed D).
 - exact (JitKRefCompatClo.JitKRefCompatClo.compat_lambda sealed D).
 - exact (JitKRefCompatClo.JitKRefCompatClo.compat_freeze sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_call sealed D).
 - exact (JitKRefFund.JitKRefFund.compat_app sealed D).
 - exact Dw.
Qed.

(* ======================= uncurrying is not a KRef refinement ======================= *)
(* F is a partial application of g, of arity 2, with nothing applied yet. The source (F 1 2)
   calls g with both arguments and returns 1. The witness ((F 1) 2) calls g with one argument,
   which jit_rules refuses (arity errors), and raises XArity. Every throw the source can reach is
   a resource error, so KRef fails. D is empty, so D_wf holds, and VRel relates F's value to
   itself at every index. *)
Definition ux_f : name := of_string "F".
Definition ux_g : name := of_string "g".
Definition ux_x : name := of_string "x".
Definition ux_y : name := of_string "y".
Definition ux_one : expr := ENum (NInt 1).
Definition ux_two : expr := ENum (NInt 2).
Definition ux_src : expr := EApp (EVar ux_f) [ux_one; ux_two].
Definition ux_tgt : expr := EApp (EApp (EVar ux_f) [ux_one]) [ux_two].
Definition ux_s : store := Store [] [] [(ux_g, FUser [ux_x; ux_y] (EVar ux_x))].
Definition ux_rho : lenv := [(ux_f, VPartial ux_g [])].
Definition ux_v1 : value := VNum (NInt 1).
Definition ux_v2 : value := VNum (NInt 2).
Definition ux_fv : value := VPartial ux_g [].
Definition ux_k1 : frame := KHead [ux_one; ux_two] ux_rho.
Definition ux_k2 : frame := KArgs ux_fv [] [ux_two] ux_rho.
Definition ux_k3 : frame := KArgs ux_fv [ux_v1] [] ux_rho.
Definition ux_body_env : lenv := [(ux_x, ux_v1); (ux_y, ux_v2)].
Definition ux_det : list config :=
 [Cfg (Eval ux_rho ux_src) [] ux_s; Cfg (Eval ux_rho (EVar ux_f)) [ux_k1] ux_s;
  Cfg (Ret ux_fv) [ux_k1] ux_s; Cfg (Eval ux_rho ux_one) [ux_k2] ux_s;
  Cfg (Ret ux_v1) [ux_k2] ux_s; Cfg (Eval ux_rho ux_two) [ux_k3] ux_s;
  Cfg (Ret ux_v2) [ux_k3] ux_s; Cfg (Eval ux_body_env (EVar ux_x)) [] ux_s;
  Cfg (Ret ux_v1) [] ux_s].

Section Ux.
Variable sealed : list name.
Notation R := (jit_rules sealed).
Notation P := jit_profile.

Definition ux_inv (c : config) : Prop :=
 In c ux_det \/ exists x, (exists r, resource_exn R r = Some x) /\
   In c [Cfg (Throw x) [ux_k1] ux_s; Cfg (Throw x) [ux_k2] ux_s; Cfg (Throw x) [ux_k3] ux_s; Cfg (Throw x) [] ux_s].

Lemma ux_inv_step : forall c l c1, step_r R P c l c1 -> ux_inv c -> ux_inv c1.
Proof.
 intros c l c1 St [I|(x & Rx & I)].
 - cbn in I. repeat destruct I as [<-|I]; try contradiction; inversion St; subst;
   repeat match goal with E : next_r _ _ _ = _ |- _ => vm_compute in E end; try discriminate;
   try match goal with E : MTau _ = MTau _ |- _ => injection E as <-; left; vm_compute; tauto end;
   match goal with Rx : resource_exn _ ?r = Some ?y |- _ =>
     right; exists y; split; [exists r; exact Rx|cbn; tauto] end.
 - cbn in I. repeat destruct I as [<-|I]; try contradiction; inversion St; subst;
   repeat match goal with E : next_r _ _ _ = _ |- _ => vm_compute in E end;
   repeat match goal with E : running_state _ = _ |- _ => vm_compute in E end; try discriminate;
   match goal with E : MTau _ = MTau _ |- _ => injection E as <- end;
   right; exists x; (split; [exact Rx|cbn; tauto]).
Qed.

Lemma ux_inv_star : forall c t c', star (step_r R P) c t c' -> ux_inv c -> ux_inv c'.
Proof. intros c t c' H. induction H as [|c l c1 t c2 St _ IH]; intros I; [exact I|apply IH; exact (ux_inv_step _ _ _ St I)]. Qed.

Lemma ux_runs_tau : forall n c c1 c2, next_r R P c = MTau c1 ->
 K.runs sealed n c1 [] c2 -> K.runs sealed (S n) c [] c2.
Proof. intros n c c1 c2 E H. exact (K.runs_S sealed n c Tau c1 [] c2 (step_r_tau R P c c1 E) H). Qed.

Lemma ux_tgt_runs : K.runs sealed 7 (Cfg (Eval ux_rho ux_tgt) [] ux_s) [] (Cfg (Throw XArity) [] ux_s).
Proof. do 7 (eapply ux_runs_tau; [reflexivity|]). constructor. Qed.

Theorem uncurry_not_kref : ~ K.KRef sealed [] [ux_f] ux_src ux_tgt.
Proof.
 intros H.
 assert (W0 : K.wf_world []) by (split; constructor).
 assert (HE : K.EnvRel_with (K.VRel sealed [] 20) [] [ux_f] ux_rho ux_rho).
 { intros x [<-|[]]. exists ux_fv, ux_fv. split; [reflexivity|split; [reflexivity|]].
   rewrite (KG.VRel_unfold sealed [] 20). cbn. split; reflexivity. }
 pose proof (H 20%nat [] ux_rho ux_rho W0 HE) as E.
 assert (HK : K.KRel sealed [] 20 [] [] []) by exact (KG.KRel_top sealed [] 20 [] W0).
 assert (HS : K.SRel sealed [] 20 [] ux_s ux_s).
 { assert (SH : K.StoreHas [] ux_s) by (intros f d []).
   unfold K.SRel, K.SRel_with.
   split; [exact W0|split; [exact SH|split; [exact SH|split; [reflexivity|split; [constructor|]]]]].
   intros l0 l []. }
 pose proof (E 20%nat (le_n _) [] (KG.wext_refl [] W0) [] [] HK ux_s ux_s HS) as O.
 destruct (O 7%nat [] _ ltac:(lia) ux_tgt_runs) as (_ & B & _).
 destruct (B _ _ eq_refl) as (s0 & w' & S0 & _).
 destruct (ux_inv_star _ _ _ S0 (or_introl (or_introl eq_refl))) as [I|(x & (r & Rx) & I)].
 - cbn in I. repeat destruct I as [Ec|I]; try discriminate; contradiction.
 - cbn in I. repeat destruct I as [Ec|I]; try discriminate; try contradiction.
   injection Ec as -> _. destruct r; discriminate.
Qed.
End Ux.

(* ======================= tests (not evidence of anything general) ======================= *)
Definition t_D : list (name * fundef) := [(plus_name, FPrim PAdd); (minus_name, FPrim PSub)].
(* (+ (- 5 2) 4) folds to 7 with + and - in D ... *)
Example cf_fold_nested : cf_chk t_D 3 [] (ECall plus_name [ECall minus_name [ENum (NInt 5); ENum (NInt 2)]; ENum (NInt 4)]) (ENum (NInt 7)) = true.
Proof. vm_compute. reflexivity. Qed.
(* ... not to anything else ... *)
Example cf_fold_wrong : cf_chk t_D 3 [] (ECall plus_name [ENum (NInt 5); ENum (NInt 2)]) (ENum (NInt 8)) = false.
Proof. vm_compute. reflexivity. Qed.
(* ... and not without + in D ... *)
Example cf_fold_no_prim : cf_chk [] 3 [] (ECall plus_name [ENum (NInt 5); ENum (NInt 2)]) (ENum (NInt 7)) = false.
Proof. vm_compute. reflexivity. Qed.
(* ... nor past the fixnum range, where + raises. *)
Example cf_fold_overflow : cf_chk t_D 3 [] (ECall plus_name [ENum (NInt JitBytecode.JitBytecode.fix_max); ENum (NInt 1)])
 (ENum (NInt (JitBytecode.JitBytecode.fix_max + 1))) = false.
Proof. vm_compute. reflexivity. Qed.
(* A folded list constant: the witness's erasure is the source, accepted by congruence. *)
Example cf_fold_cons : forall e, N.erase [] (N.NConst (VCons (VNum (NInt 1)) (VCons (VSym (of_string "a")) VNil))) = Some e ->
 cf_chk [] 10 [] (ECall N.cons_name [ENum (NInt 1); ECall N.cons_name [ESym (of_string "a"); ENil]]) e = true.
Proof. intros e H. vm_compute in H. injection H as <-. vm_compute. reflexivity. Qed.
(* The uncurried witness is rejected. *)
Example cf_uncurry_rejected : cf_chk [] 10 [ux_f] ux_src ux_tgt = false.
Proof. vm_compute. reflexivity. Qed.
End JitFrontCopyFold.
