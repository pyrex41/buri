(* Shen/JIT Phase 2, front track, r1-f-copy-fold-apply: norm's constant folding (cons, + and -),
   dynamic-application uncurrying, and freeze and lambda copying, against KRef.

   What lower.shen does (934cfa5, src/lowerer/lower.shen, `shen-jit.lower.prim`, `norm-apply`,
   `let-frozen`, `frozen-in`, `frozen-late`, `let-lambda`, `apply-in`, `inline-frozen`), and what
   this file proves of each:

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
     own premise, checked by the checker (d_has), never assumed. It is NECESSARY, not an artefact
     of the proof: fold_arith_needs_store proves, with no premise, ~ KRef sealed [] [] (+ 1 2) 3,
     from a store (allowed by SRel, which asks only StoreHas D) where + is a user function
     returning its first argument. JitFrontD's interface item 2 says a D built by D_of never holds
     + or - (they are not in stage 0's sealed list), so on real D stores fold-arith (and the 6
     folding `vector` inline sites) is accepted only once that item is settled (OB-JIT-LOWER-FRONT);
     Example cf_fold_no_prim pins the rejection. A candidate fix, outside this file: + and - are
     fixed names (JitProfile.is_fixed_name; defun of one raises, jit_defun_fixed_refused), so a
     store reachable under jit_rules keeps their primitive binding; K.D_wf (every D name sealed)
     would have to admit fixed-name FPrim entries, with a fixed_stable lemma like sealed_stable.
   - dynamic application: norm-apply turns (F A B) into ((F A) B). Erased, the source is
     EApp F [A; B] and the witness EApp (EApp F [A]) [B]. This is NOT a KRef refinement:
     uncurry_not_kref proves, with no premise, that for F bound to a partial application
     (VPartial g [] for a g of arity 2, a value VRel relates to itself) the source returns while
     the target raises XArity (jit_rules has arity errors, so a partial call of one argument
     raises), which no source run can match. So no sound checker accepts this rewrite against
     KRef as it stands; neither cf_chk nor cc does. (A second, independent failure for a non-atomic
     B is the evaluation order: the source evaluates B before applying F to A, the witness after.)
     What it would take is a design decision outside this file: either erase maps an apply chain
     back to the multi-argument EApp of the source, or KRef's environments exclude partial
     applications. Either changes a reviewed statement and is Reuben's call
     (OB-JIT-FRONT-UNCURRY). Where F is a KNOWN lambda (let-lambda below) the rewrite is sound
     and cc accepts it.
     Two facts for that decision. (a) Under jit_rules no VPartial value is ever made: arity_errors
     is true, so KLPort.call_named_r's arity_mismatch raises XArity before its Nat.ltb branch could
     return a VPartial (shen-jit's semantics.md s9 at 934cfa5: applying a closure to too few
     arguments raises). The counterexample's value is one VRel relates but no jit_rules run makes,
     so excluding VPartial from KRef's environments is one candidate fix; for a non-atomic
     trailing argument the evaluation order (above) also needs atomic trailing arguments or a
     let-binding of them in lower.shen. (b) The rewrite never fires in stage 0: uncurry_scan, run
     by stage0_to_rocq.py --uncurry over the 955 parsed stage 0 sources (Rocq vm_compute; a test,
     not proof), finds 0 dynamic applications of two or more arguments (0 with a non-atomic
     trailing argument). So OB-JIT-FRONT-UNCURRY changes no stage 0 verdict.
   - freeze and lambda copying: a KNOWN-CLOSURE relation, KRefF F g e0 e: e refines e0 in scope g
     from every pair of related environments that also meets the entries F. An entry (kc) names a
     let-bound closure the source made and the target copied away: KF X E0 gl for
     (let X (freeze E0) ...), KL X P Ps I0 gl for (let X (lambda P (lambda P1 ... I0)) ...). Its
     invariant (kc_inv): the SOURCE environment binds X to exactly that closure, and the closure's
     captured environment is EnvRel-related on gl (E0's free names) to the TARGET's current
     environment. KRefF [] g = KRef g (KRefF_nil). The invariant is what KRef's own environment
     relation cannot carry (the target has no X at all), so the congruence of KRefF is proved
     from the ERel-level lemmas the KRef compat statements are themselves proved from
     (JitKRefCompatCtl.ERel_let/if/and/or/cond/type/trap, JitKRefCompatClo.lam_core/frz_core/
     compat_app_core, JitKRefCompatCall.compat_call_core), under Section hypotheses naming
     fund_gen_statement and prim_compat_statement (which those lemmas need below the index) and
     cf_chk's soundness; cc_sound then instantiates them with JitKRefFund.fund_gen,
     JitKRefPrim.prim_compat and cf_chk_sound. This is not a weakening: KRefF's conclusion is
     ERel, and at F = [] its premise is KRef's.
     Rules (each a lemma, each closed):
       KRefF_letfrz / KRefF_letlam: the source let (silent steps, one source-only cell, then
         anti-reduction, KB.ERel_anti) adds the entry; the body is checked with X out of scope
         (rem x g), so the source closure is never compared with a target value, and entries the
         let would shadow are dropped.
       KRefF_thaw / KRefF_thaw_call: (X) or (thaw X) (the latter with the kernel's thaw body in D,
         JitFrontD.D_has_kernel_thaw's shape, checked by d_has) against the copy E: the source runs
         E0 in the closure's environment, related on gl to the target's (ERel_thaw_site).
       KRefF_lamsite: (X A1 ... An), n the number of parameters, against
         (let P A1' (let P1 A2' ... I)): a simulation in which the source evaluates every argument
         (KArgs) while the target binds each in turn (KLet), then the source applies the curried
         closure (apply_chain: one source-only cell per inner lambda) and both run the body
         (lam_krel, ERel_lam_site). The arguments are checked in a scope without the parameters
         (reml), so a target let cannot capture one.
       Congruence (KRefF_let/lam/if/and/or/cond/type/trap/frz/app/call): a binder drops the
         entries whose name or free names it rebinds (drop, Inv_bind), closures made in the body
         capture the entries' environment (Inv_tag).
     The checker cc (hook, D, fuel, entries, scope, source, witness) tries cf_chk, a hook, the
     thaw and lambda sites, the two intro rules, the bind site and congruence. cc_sound: D_wf and the hook's
     soundness give KRef; copy_chk_sound: with no hook, D_wf alone.
       KRefF_bindsite (cc_bind, cc_bind_sound): bound-now under a known frozen closure.
         lower.shen copies a let-bound freeze only when frozen-binds? holds, so every let-frozen
         copy has a (shen.bind! A B C X) use, which frozen-in turns into bound-now's expansion with
         E copied in. The rule is JitFrontProlog.bind_rule's checks with the fourth argument the
         entry's name X instead of (freeze E0): the source reads X (KRel_ca_lastvar, no new cell)
         and JitFrontProlog.beq_sound runs with the closure's captured environment and the entry's
         scope gl (its HE is the entry's EnvRel on gl). Each copied place is checked against E0 in
         KRef, in the scope of its free names in gl; Y0 and B0 are checked with the entries the
         earlier lets may shadow dropped. Examples cc_bind_copy / cc_bind_wrong_body /
         cc_bind_shadow are tests.
     What this does NOT cover (census, CENSUS.md: let-frozen-copy 5 definitions, frozen-late-hoist
     3, inline-frozen 6, let-lambda 6):
       - every D holding shen.bind! fails D_compiled' today (JitFrontD's D_why: shen-jit.pvar-offset,
         OB-JIT-PORT-PRIMS), so the let-frozen-copy definitions stay residual in the full pipeline
         whatever cc_bind proves; and cc_bind needs shen.bind!'s and do's bodies in D.
       - inline-frozen: an inlined parameter bound to (freeze E) and thawed once. ERel_thaw_site
         and KRefF_thaw are the lemmas F-inline's inline-site rule can use; the site rule itself
         is F-inline's.
       - frozen-late-hoist: (if C1 Y1 (if C2 Y2 false)) to (if (or C1 C2) (let X (freeze E)
         (if C1 Y1 Y2)) false) evaluates C1 twice in the target; needs a target-side purity and
         determinism lemma for simple tests, and simple-test? admits shen-jit.pvar?, a port
         primitive with no source meaning (OB-JIT-PORT-PRIMS). Not proved here.
       - real-data counts: cc has not been run over whole stage 0 definitions. Alone it cannot
         accept one that needs another family's rewrite (inline, sugar, ...), so a per-definition
         count for cc alone would say nothing; the composed front checker is the merge's. How many
         of the 955 it helps accept is UNKNOWN (the source judge's 148 of 955 is unchanged by this
         file). cc_bind's structural part is beq, the same check r1-f-prolog's bind_rule_report
         ran on all 37 real bound-now sites (37 accepted, a test), which include the let-frozen
         ones; cc_bind was not run on them.
     Ledger: OB-JIT-FRONT-COPY.

   The checker cf_chk (fuel, scope, source, witness) accepts: equal literals; a variable in scope;
   the same head constructor with the parts accepted (the scope extended under let, lambda);
   and fold-arith. It is proved sound first under Section hypotheses naming KRef's compat_*
   statements (cf_chk_sound_hyp), then instantiated with JitKRefCompatCtl, JitKRefCompatClo and
   JitKRefFund, so cf_chk_sound has D_wf as its only premise.

   Proved here (each in Audit_Jit, "Closed under the global context"): fold_cons_erase, cfold_run,
   ERel_src_ret, fold_arith_kref, cf_chk_sound_hyp, cf_chk_sound, uncurry_not_kref,
   fold_arith_needs_store, KRefF_nil, KRefF_let, KRefF_lam, KRefF_letfrz, KRefF_letlam,
   ERel_thaw_site, KRefF_thaw, KRefF_thaw_call, apply_chain, lam_krel, ERel_lam_site, KRefF_lamsite,
   cc_same_sound, cc_sound_hyp, cc_sound, copy_chk_sound, KRel_ca_lastvar, KRefF_bindsite,
   cc_bind_sound.
   Tests, not evidence of anything general: the Examples at the end.
   No axioms, nothing Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase JitKRefCompatCtl JitKRefCompatClo JitKRefCompatCall JitKRefFv JitKRefPrim JitKRefFund JitLowerStage0 JitNorm JitFrontD JitFrontProlog.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontCopyFold.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel.
Module K := JitKRef.JitKRef.
Module KB := JitKRefBase.JitKRefBase.
Module KG := JitKRefGround.JitKRefGround.
Module N := JitNorm.JitNorm.
Module CC := JitKRefCompatCtl.JitKRefCompatCtl.
Module CL := JitKRefCompatClo.JitKRefCompatClo.
Module CA := JitKRefCompatCall.JitKRefCompatCall.
Module FD := JitFrontD.JitFrontD.
Module PL := JitFrontProlog.JitFrontProlog.

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

(* ======================= known closures ======================= *)
Definition lamc (ps : list name) (b : expr) : expr := fold_right ELam b ps.

(* A let-bound closure the source made and the target copied away: X bound to (freeze E0), or
   to (lambda P (lambda P1 ... (lambda Pn I0))), whose free names are in gl. *)
Inductive kc := KF (x : name) (e0 : expr) (gl : list name)
              | KL (x : name) (p : name) (ps : list name) (i0 : expr) (gl : list name).

Definition kc_x (c : kc) : name := match c with KF x _ _ | KL x _ _ _ _ => x end.
Definition kc_gl (c : kc) : list name := match c with KF _ _ gl | KL _ _ _ _ gl => gl end.
Definition memb (y : name) (l : list name) : bool := existsb (text_eqb y) l.
(* The entries a binder y leaves intact: neither the closure's name nor one of its free names. *)
Definition kc_keep (y : name) (c : kc) : bool := negb (memb y (kc_x c :: kc_gl c)).
Definition drop (y : name) (F : list kc) : list kc := filter (kc_keep y) F.
Definition dropl (ys : list name) (F : list kc) : list kc := filter (fun c => forallb (fun y => kc_keep y c) ys) F.
Definition rem (y : name) (g : list name) : list name := filter (fun z => negb (text_eqb z y)) g.
Definition reml (ys : list name) (g : list name) : list name := filter (fun z => negb (memb z ys)) g.

Fixpoint lets (xs : list name) (vs : list expr) (b : expr) : expr := match xs, vs with
 | x :: xs, v :: vs => ELet x v (lets xs vs b)
 | _, _ => b end.

Lemma memb_In : forall y l, memb y l = true <-> In y l.
Proof.
 intros y l. unfold memb. rewrite existsb_exists. split.
 - intros (z & I & E). apply text_eqb_eq in E. subst. exact I.
 - intros I. exists y. split; [exact I|apply text_eqb_refl].
Qed.

Lemma memb_false : forall y l, memb y l = false <-> ~ In y l.
Proof.
 intros y l. split.
 - intros E I. apply memb_In in I. congruence.
 - intros N. destruct (memb y l) eqn:E; [apply memb_In in E; contradiction|reflexivity].
Qed.

Lemma lookup_cons_ne : forall {A} (y x : name) (a : A) l, y <> x -> lookup y ((x, a) :: l) = lookup y l.
Proof.
 intros A y x a l N. cbn. destruct (text_eqb y x) eqn:E; [apply text_eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma lookup_app_notin : forall {A} (y : name) (l1 l2 : list (name * A)), ~ In y (map fst l1) ->
 lookup y (l1 ++ l2) = lookup y l2.
Proof.
 intros A y l1 l2. induction l1 as [|[x a] l1 IH]; intros N; [reflexivity|].
 cbn [app]. rewrite lookup_cons_ne; [apply IH; intros I; apply N; right; exact I|].
 intros ->. apply N. left. reflexivity.
Qed.

Lemma In_rem : forall y z g, In z (rem y g) <-> In z g /\ z <> y.
Proof.
 intros y z g. unfold rem. rewrite filter_In. split.
 - intros [I E]. split; [exact I|]. intros ->. rewrite text_eqb_refl in E. discriminate.
 - intros [I N]. split; [exact I|]. destruct (text_eqb z y) eqn:E; [apply text_eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma In_reml : forall ys z g, In z (reml ys g) <-> In z g /\ ~ In z ys.
Proof.
 intros ys z g. unfold reml. rewrite filter_In. split.
 - intros [I E]. split; [exact I|]. apply negb_true_iff in E. apply memb_false. exact E.
 - intros [I N]. split; [exact I|]. apply negb_true_iff. apply memb_false. exact N.
Qed.

Lemma In_drop : forall y c F, In c (drop y F) <-> In c F /\ y <> kc_x c /\ ~ In y (kc_gl c).
Proof.
 intros y c F. unfold drop, kc_keep. rewrite filter_In. split.
 - intros [I E]. apply negb_true_iff, memb_false in E. split; [exact I|].
   split; [intros ->; apply E; left; reflexivity|intros I'; apply E; right; exact I'].
 - intros (I & N1 & N2). split; [exact I|]. apply negb_true_iff, memb_false.
   intros [E|E]; [apply N1; symmetry; exact E|contradiction].
Qed.

Lemma In_dropl : forall ys c F, In c (dropl ys F) <-> In c F /\ (forall y, In y ys -> y <> kc_x c /\ ~ In y (kc_gl c)).
Proof.
 intros ys c F. unfold dropl. rewrite filter_In, forallb_forall. split.
 - intros [I H]. split; [exact I|]. intros y Iy. specialize (H y Iy). unfold kc_keep in H.
   apply negb_true_iff, memb_false in H. split; [intros ->; apply H; left; reflexivity|intros I'; apply H; right; exact I'].
 - intros [I H]. split; [exact I|]. intros y Iy. destruct (H y Iy) as [N1 N2]. unfold kc_keep.
   apply negb_true_iff, memb_false. intros [E|E]; [apply N1; symmetry; exact E|contradiction].
Qed.

Section Rel.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation VRel := (K.VRel sealed D).
Notation ERel := (K.ERel sealed D).
Notation KRel := (K.KRel sealed D).
Notation SRel := (K.SRel sealed D).
Notation KRef := (K.KRef sealed D).
Notation EnvRel := K.EnvRel_with.
Notation srun := (K.srun sealed).
Notation ObsT := (K.ObsT sealed).

(* The invariant of an entry in environments rho0 (source) and rho (target): the source binds X
   to exactly that closure, whose captured environment is related on gl to the TARGET's current
   one. Neither X nor gl (nor a lambda's parameters) is the closure-identity key. *)
Definition kc_inv (k : nat) (w : K.world) (c : kc) (rho0 rho : lenv) : Prop :=
 match c with
 | KF x e0 gl => x <> id_key /\ ~ In id_key gl /\
     exists r0, lookup x rho0 = Some (VFrozen e0 r0) /\ EnvRel (VRel k) w gl r0 rho
 | KL x p ps i0 gl => x <> id_key /\ ~ In id_key gl /\ ~ In id_key (p :: ps) /\
     exists r0, lookup x rho0 = Some (VLam p (lamc ps i0) r0) /\ EnvRel (VRel k) w gl r0 rho
 end.

Definition Inv (k : nat) (w : K.world) (F : list kc) (rho0 rho : lenv) : Prop :=
 forall c, In c F -> kc_inv k w c rho0 rho.

(* e refines e0 in scope g from every pair of related environments meeting the entries F. With
   F = [] it is KRef. *)
Definition KRefF (F : list kc) (g : list name) (e0 e : expr) : Prop :=
 forall k w rho0 rho, K.wf_world w -> EnvRel (VRel k) w g rho0 rho -> Inv k w F rho0 rho -> ERel k w rho0 e0 rho e.

Lemma KRefF_nil : forall g e0 e, KRefF [] g e0 e <-> KRef g e0 e.
Proof.
 intros g e0 e. split.
 - intros H k w rho0 rho W HE. apply H; [exact W|exact HE|intros c []].
 - intros H k w rho0 rho W HE _. apply H; assumption.
Qed.

Lemma KRefF_of_KRef : forall F g e0 e, KRef g e0 e -> KRefF F g e0 e.
Proof. intros F g e0 e H k w rho0 rho W HE _. apply H; assumption. Qed.

(* ---------- environments ---------- *)
Lemma EnvRel_incl : forall V w g g' r0 r, incl g g' -> EnvRel V w g' r0 r -> EnvRel V w g r0 r.
Proof. intros V w g g' r0 r I H y Iy. apply H. apply I. exact Iy. Qed.

Lemma EnvRel_lookup : forall V w g r0 r r0' r', (forall y, In y g -> lookup y r0' = lookup y r0) ->
 (forall y, In y g -> lookup y r' = lookup y r) -> EnvRel V w g r0 r -> EnvRel V w g r0' r'.
Proof. intros V w g r0 r r0' r' E0 E H y Iy. rewrite (E0 y Iy), (E y Iy). apply H. exact Iy. Qed.

Lemma kc_inv_mono : forall k j w w' c rho0 rho, (j <= k)%nat -> K.wext w w' -> kc_inv k w c rho0 rho -> kc_inv j w' c rho0 rho.
Proof.
 intros k j w w' [x e0 gl|x p ps i0 gl] rho0 rho L W H; cbn in H |- *.
 - destruct H as (N1 & N2 & r0 & E & HE). split; [exact N1|split; [exact N2|]].
   exists r0. split; [exact E|eapply KB.EnvRel_mono; eauto].
 - destruct H as (N1 & N2 & N3 & r0 & E & HE). split; [exact N1|split; [exact N2|split; [exact N3|]]].
   exists r0. split; [exact E|eapply KB.EnvRel_mono; eauto].
Qed.

Lemma Inv_mono : forall k j w w' F rho0 rho, (j <= k)%nat -> K.wext w w' -> Inv k w F rho0 rho -> Inv j w' F rho0 rho.
Proof. intros k j w w' F rho0 rho L W H c I. eapply kc_inv_mono; [exact L|exact W|apply H; exact I]. Qed.

(* An entry survives any change of the environments that keeps the source's lookup of its name
   and the target's lookups of its free names. *)
Lemma kc_inv_lookup : forall k w c rho0 rho rho0' rho',
 lookup (kc_x c) rho0' = lookup (kc_x c) rho0 -> (forall y, In y (kc_gl c) -> lookup y rho' = lookup y rho) ->
 kc_inv k w c rho0 rho -> kc_inv k w c rho0' rho'.
Proof.
 intros k w [x e0 gl|x p ps i0 gl] rho0 rho rho0' rho' E0 E H; cbn in E0, E, H |- *.
 - destruct H as (N1 & N2 & r0 & L & HE). split; [exact N1|split; [exact N2|]].
   exists r0. rewrite E0. split; [exact L|]. eapply EnvRel_lookup; [intros; reflexivity|exact E|exact HE].
 - destruct H as (N1 & N2 & N3 & r0 & L & HE). split; [exact N1|split; [exact N2|split; [exact N3|]]].
   exists r0. rewrite E0. split; [exact L|]. eapply EnvRel_lookup; [intros; reflexivity|exact E|exact HE].
Qed.

Lemma Inv_bind : forall k w F rho0 rho y a0 a, Inv k w F rho0 rho -> Inv k w (drop y F) ((y, a0) :: rho0) ((y, a) :: rho).
Proof.
 intros k w F rho0 rho y a0 a H c I. apply In_drop in I as (I & N1 & N2).
 eapply kc_inv_lookup; [| |apply H; exact I].
 - apply lookup_cons_ne. intros E. apply N1. symmetry. exact E.
 - intros z Iz. apply lookup_cons_ne. intros ->. contradiction.
Qed.

Lemma Inv_tag : forall k w F rho0 rho a0 a, Inv k w F rho0 rho -> Inv k w F ((id_key, a0) :: rho0) ((id_key, a) :: rho).
Proof.
 intros k w F rho0 rho a0 a H c I. pose proof (H c I) as Hc.
 assert (Nx : kc_x c <> id_key /\ ~ In id_key (kc_gl c)) by (destruct c; cbn in Hc |- *; tauto).
 eapply kc_inv_lookup; [| |exact Hc].
 - apply lookup_cons_ne. exact (proj1 Nx).
 - intros z Iz. apply lookup_cons_ne. intros ->. exact (proj2 Nx Iz).
Qed.

Lemma Inv_src : forall k w F rho0 rho y a0, Inv k w F rho0 rho -> Inv k w (drop y F) ((y, a0) :: rho0) rho.
Proof.
 intros k w F rho0 rho y a0 H c I. apply In_drop in I as (I & N1 & N2).
 eapply kc_inv_lookup; [| |apply H; exact I].
 - apply lookup_cons_ne. intros E. apply N1. symmetry. exact E.
 - intros z Iz. reflexivity.
Qed.

Lemma Inv_tgt_app : forall k w F rho0 rho ys ext, (forall y, In y (map fst ext) -> In y ys) ->
 Inv k w F rho0 rho -> Inv k w (dropl ys F) rho0 (ext ++ rho).
Proof.
 intros k w F rho0 rho ys ext Hy H c I. apply In_dropl in I as (I & N).
 eapply kc_inv_lookup; [reflexivity| |apply H; exact I].
 intros z Iz. apply lookup_app_notin. intros Iz'. destruct (N z (Hy z Iz')) as [_ N2]. contradiction.
Qed.

Lemma Inv_sub : forall k w F F' rho0 rho, incl F' F -> Inv k w F rho0 rho -> Inv k w F' rho0 rho.
Proof. intros k w F F' rho0 rho I H c Ic. apply H. apply I. exact Ic. Qed.

Lemma drop_incl : forall y F, incl (drop y F) F.
Proof. intros y F c I. apply In_drop in I. tauto. Qed.

(* ---------- the fundamental property below every index ---------- *)
Section Cong.
Hypotheses (FG : K.fund_gen_statement sealed D) (PC : K.prim_compat_statement sealed D) (Dw : K.D_wf sealed D).

Lemma fb : forall k, K.fund_below sealed D k.
Proof. intros [|k]; [intros j L; lia|exact (FG Dw k)]. Qed.

Ltac envs := match goal with
 | |- K.wf_world _ => match goal with W : K.wext _ ?w' |- K.wf_world ?w' => exact (proj2 W) end
 | _ => idtac end.

Lemma KRefF_let : forall F g x a0 a b0 b, KRefF F g a0 a -> KRefF (drop x F) (x :: g) b0 b ->
 KRefF F g (ELet x a0 b0) (ELet x a b).
Proof.
 intros F g x a0 a b0 b Ha Hb k w rho0 rho W HE HI. apply CC.ERel_let; [apply Ha; assumption|].
 intros j w' v0 v L W' HV. apply Hb; [exact (proj2 W')| |].
 - apply CC.env_cons; [eapply KB.EnvRel_mono; eauto|exact HV].
 - apply Inv_bind. eapply Inv_mono; eauto.
Qed.

Lemma KRefF_if : forall F g c0 c a0 a b0 b, KRefF F g c0 c -> KRefF F g a0 a -> KRefF F g b0 b ->
 KRefF F g (EIf c0 a0 b0) (EIf c a b).
Proof. intros F g c0 c a0 a b0 b Hc Ha Hb k w rho0 rho W HE HI. apply CC.ERel_if; [apply Hc|apply Ha|apply Hb]; assumption. Qed.

Lemma KRefF_and : forall F g a0 a b0 b, KRefF F g a0 a -> KRefF F g b0 b -> KRefF F g (EAnd a0 b0) (EAnd a b).
Proof. intros F g a0 a b0 b Ha Hb k w rho0 rho W HE HI. apply CC.ERel_and; [apply Ha|apply Hb]; assumption. Qed.

Lemma KRefF_or : forall F g a0 a b0 b, KRefF F g a0 a -> KRefF F g b0 b -> KRefF F g (EOr a0 b0) (EOr a b).
Proof. intros F g a0 a b0 b Ha Hb k w rho0 rho W HE HI. apply CC.ERel_or; [apply Ha|apply Hb]; assumption. Qed.

Lemma KRefF_type : forall F g a0 a, KRefF F g a0 a -> KRefF F g (EType a0) (EType a).
Proof. intros F g a0 a Ha k w rho0 rho W HE HI. apply CC.ERel_type. apply Ha; assumption. Qed.

Lemma KRefF_cond : forall F g cl0 cl, Forall2 (fun p0 p => KRefF F g (fst p0) (fst p) /\ KRefF F g (snd p0) (snd p)) cl0 cl ->
 KRefF F g (ECond cl0) (ECond cl).
Proof.
 intros F g cl0 cl H k w rho0 rho W HE HI. apply CC.ERel_cond.
 eapply Forall2_impl; [|exact H]. intros p0 p [H1 H2]. split; [apply H1|apply H2]; assumption.
Qed.

Lemma KRefF_trap : forall F g a0 a h0 h, KRefF F g a0 a -> KRefF F g h0 h -> KRefF F g (ETrap a0 h0) (ETrap a h).
Proof.
 intros F g a0 a h0 h Ha Hh k w rho0 rho W HE HI.
 apply CC.ERel_trap; [exact (CC.AppExn_of sealed D PC k (fb k))|apply Ha|apply Hh]; assumption.
Qed.

Lemma KRefF_lam : forall F g x b0 b, KRefF (drop x F) (x :: g) b0 b -> KRefF F g (ELam x b0) (ELam x b).
Proof.
 intros F g x b0 b Hb k w rho0 rho W HE HI. apply CL.lam_core. intros j w' l0 l a0 a L W' I A.
 apply Hb; [exact (proj2 W')| |].
 - apply (CL.EnvRel_arg sealed D j w' g); [|exact A].
   apply (EnvRel_incl _ _ g (id_key :: g)); [intros y Iy; right; exact Iy|].
   apply CL.EnvRel_tagged; [|exact I]. eapply KB.EnvRel_mono; [|exact W'|exact HE]. lia.
 - apply Inv_bind. apply Inv_tag. eapply Inv_mono; [|exact W'|exact HI]. lia.
Qed.

Lemma KRefF_frz : forall F g b0 b, KRefF F g b0 b -> KRefF F g (EFreeze b0) (EFreeze b).
Proof.
 intros F g b0 b Hb k w rho0 rho W HE HI. apply CL.frz_core. intros j w' l0 l L W' I.
 apply Hb; [exact (proj2 W')| |].
 - apply (EnvRel_incl _ _ g (id_key :: g)); [intros y Iy; right; exact Iy|].
   apply CL.EnvRel_tagged; [|exact I]. eapply KB.EnvRel_mono; [|exact W'|exact HE]. lia.
 - apply Inv_tag. eapply Inv_mono; [|exact W'|exact HI]. lia.
Qed.

Lemma Forall2_below : forall F g k w rho0 rho as0 as1, K.wf_world w -> EnvRel (VRel k) w g rho0 rho -> Inv k w F rho0 rho ->
 Forall2 (KRefF F g) as0 as1 ->
 Forall2 (fun a0 a => forall j w', (j < k)%nat -> K.wext w w' -> ERel j w' rho0 a0 rho a) as0 as1.
Proof.
 intros F g k w rho0 rho as0 as1 W HE HI H. eapply Forall2_impl; [|exact H]. intros a0 a Ha j w' L W'.
 apply Ha; [exact (proj2 W')|eapply KB.EnvRel_mono; [|exact W'|exact HE]; lia|eapply Inv_mono; [|exact W'|exact HI]; lia].
Qed.

Lemma KRefF_app : forall F g h0 h as0 as1, KRefF F g h0 h -> Forall2 (KRefF F g) as0 as1 ->
 KRefF F g (EApp h0 as0) (EApp h as1).
Proof.
 intros F g h0 h as0 as1 Hh Ha k w rho0 rho W HE HI. apply CL.compat_app_core; [exact (fb k)|exact PC| |].
 - intros j w' L W'. apply Hh; [exact (proj2 W')|eapply KB.EnvRel_mono; [|exact W'|exact HE]; lia|eapply Inv_mono; [|exact W'|exact HI]; lia].
 - eapply Forall2_below; eauto.
Qed.

Lemma KRefF_call : forall F g f as0 as1, Forall2 (KRefF F g) as0 as1 -> KRefF F g (ECall f as0) (ECall f as1).
Proof.
 intros F g f as0 as1 Ha k w rho0 rho W HE HI. apply CA.compat_call_core; [exact (fb k)|exact PC|].
 eapply Forall2_below; eauto.
Qed.
End Cong.

(* ---------- thaw of a known frozen closure ---------- *)
Lemma ERel_thaw_site : forall k w rho1 x e0 r0 rho e, lookup x rho1 = Some (VFrozen e0 r0) ->
 ERel k w r0 e0 rho e -> ERel k w rho1 (EApp (EVar x) []) rho e.
Proof.
 intros k w rho1 x e0 r0 rho e L He. eapply KB.ERel_anti_same; [|exact He]. intros K0 s0.
 eapply KB.srun_tau; [reflexivity|]. eapply KB.srun_tau; [apply KB.sval_next; exact L|].
 eapply KB.srun_tau; [reflexivity|apply KB.srun_refl].
Qed.

Lemma KRefF_thaw : forall F g x e0 gl e, In (KF x e0 gl) F -> KRef gl e0 e -> KRefF F g (EApp (EVar x) []) e.
Proof.
 intros F g x e0 gl e I He k w rho0 rho W HE HI. destruct (HI _ I) as (_ & _ & r0 & L & HE').
 eapply ERel_thaw_site; [exact L|]. apply He; assumption.
Qed.

Lemma KRefF_thaw_call : forall F g v x e0 gl e, In (FD.thaw_name, FUser [v] (EApp (EVar v) [])) D ->
 In (KF x e0 gl) F -> KRef gl e0 e -> KRefF F g (ECall FD.thaw_name [EVar x]) e.
Proof.
 intros F g v x e0 gl e Id I He k w rho0 rho W HE HI. destruct (HI _ I) as (_ & _ & r0 & L & HE').
 eapply (KB.ERel_anti_call sealed D k w FD.thaw_name [v] (EApp (EVar v) []) [EVar x] [VFrozen e0 r0]);
  [exact Id|constructor; [exact L|constructor]|reflexivity|].
 eapply ERel_thaw_site; [cbn; rewrite text_eqb_refl; reflexivity|]. apply He; assumption.
Qed.
(* ---------- the let that makes a known closure ---------- *)
Lemma EnvRel_tagged_src : forall V w gl rho0 rho s0, ~ In id_key gl -> EnvRel V w gl rho0 rho ->
 EnvRel V w gl (tagged_env rho0 s0) rho.
Proof.
 intros V w gl rho0 rho s0 N H. eapply EnvRel_lookup; [|intros; reflexivity|exact H].
 intros y Iy. unfold tagged_env. apply lookup_cons_ne. intros ->. contradiction.
Qed.

Lemma EnvRel_rem_src : forall V w g x a0 rho0 rho, EnvRel V w g rho0 rho -> EnvRel V w (rem x g) ((x, a0) :: rho0) rho.
Proof.
 intros V w g x a0 rho0 rho H y Iy. apply In_rem in Iy as [Iy N]. rewrite lookup_cons_ne by exact N. apply H. exact Iy.
Qed.

Lemma KRefF_letfrz : forall F g x e0 gl b0 b, x <> id_key -> ~ In id_key gl -> incl gl g ->
 KRefF (KF x e0 gl :: drop x F) (rem x g) b0 b -> KRefF F g (ELet x (EFreeze e0) b0) b.
Proof.
 intros F g x e0 gl b0 b Nx Ngl Ig Hb k w rho0 rho W HE HI. apply KB.ERel_anti. intros j w' K0 s0 s L W' HS.
 exists ((x, VFrozen e0 (tagged_env rho0 s0)) :: rho0), b0, (with_cell s0). split; [|split].
 - eapply KB.srun_tau; [reflexivity|]. eapply KB.srun_tau; [reflexivity|].
   eapply KB.srun_tau; [reflexivity|apply KB.srun_refl].
 - apply KB.SRel_with_cell. exact HS.
 - assert (HE' : EnvRel (VRel j) w' g rho0 rho) by (eapply KB.EnvRel_mono; [exact L|exact W'|exact HE]).
   apply Hb; [exact (proj2 W')|apply EnvRel_rem_src; exact HE'|].
   intros c [<-|Ic].
   + cbn. split; [exact Nx|split; [exact Ngl|]]. exists (tagged_env rho0 s0).
     split; [rewrite text_eqb_refl; reflexivity|]. apply EnvRel_tagged_src; [exact Ngl|].
     eapply EnvRel_incl; [exact Ig|exact HE'].
   + eapply Inv_src; [|exact Ic]. eapply Inv_mono; [exact L|exact W'|exact HI].
Qed.

Lemma KRefF_letlam : forall F g x p ps i0 gl b0 b, x <> id_key -> ~ In id_key gl -> ~ In id_key (p :: ps) -> incl gl g ->
 KRefF (KL x p ps i0 gl :: drop x F) (rem x g) b0 b -> KRefF F g (ELet x (ELam p (lamc ps i0)) b0) b.
Proof.
 intros F g x p ps i0 gl b0 b Nx Ngl Nps Ig Hb k w rho0 rho W HE HI. apply KB.ERel_anti. intros j w' K0 s0 s L W' HS.
 exists ((x, VLam p (lamc ps i0) (tagged_env rho0 s0)) :: rho0), b0, (with_cell s0). split; [|split].
 - eapply KB.srun_tau; [reflexivity|]. eapply KB.srun_tau; [reflexivity|].
   eapply KB.srun_tau; [reflexivity|apply KB.srun_refl].
 - apply KB.SRel_with_cell. exact HS.
 - assert (HE' : EnvRel (VRel j) w' g rho0 rho) by (eapply KB.EnvRel_mono; [exact L|exact W'|exact HE]).
   apply Hb; [exact (proj2 W')|apply EnvRel_rem_src; exact HE'|].
   intros c [<-|Ic].
   + cbn. split; [exact Nx|split; [exact Ngl|split; [exact Nps|]]]. exists (tagged_env rho0 s0).
     split; [rewrite text_eqb_refl; reflexivity|]. apply EnvRel_tagged_src; [exact Ngl|].
     eapply EnvRel_incl; [exact Ig|exact HE'].
   + eapply Inv_src; [|exact Ic]. eapply Inv_mono; [exact L|exact W'|exact HI].
Qed.

(* ---------- applying a known lambda to all its parameters ---------- *)
Fixpoint cells (n : nat) (s : store) : store := match n with O => s | S n => cells n (with_cell s) end.

Lemma SRel_cells : forall n k w s0 s, SRel k w s0 s -> SRel k w (cells n s0) s.
Proof. induction n as [|n IH]; intros k w s0 s H; [exact H|apply IH; apply KB.SRel_with_cell; exact H]. Qed.

(* Equal lookups away from the closure-identity key. *)
Definition eqm (E1 E2 : lenv) : Prop := forall y, y <> id_key -> lookup y E1 = lookup y E2.

Lemma lookup_app_id : forall (X Y : lenv) a y, y <> id_key -> lookup y (X ++ (id_key, a) :: Y) = lookup y (X ++ Y).
Proof.
 intros X Y a y N. induction X as [|[z b] X IH]; [apply lookup_cons_ne; exact N|].
 cbn [app lookup]. destruct (text_eqb y z); [reflexivity|exact IH].
Qed.

Lemma combine_app : forall {A B} (l1 l1' : list A) (l2 l2' : list B), List.length l1 = List.length l2 ->
 combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
 intros A B l1. induction l1 as [|a l1 IH]; intros l1' [|b l2] l2' L; cbn in L; try discriminate; [reflexivity|].
 injection L as L. cbn. rewrite IH by exact L. reflexivity.
Qed.

Lemma apply_chain : forall ps p i0 r0 v1 vs K0 s c, List.length vs = List.length ps ->
 next_r R P c = apply_value_r R P (VLam p (lamc ps i0) r0) (v1 :: vs) K0 s ->
 exists env n, srun c [] (Cfg (Eval env i0) K0 (cells n s)) /\
   eqm env (combine (rev (p :: ps)) (rev (v1 :: vs)) ++ r0).
Proof.
 induction ps as [|p2 ps IH]; intros p i0 r0 v1 vs K0 s c Lv E.
 - destruct vs; [|discriminate]. exists ((p, v1) :: r0), 0%nat. split.
   + eapply KB.srun_tau; [rewrite E; reflexivity|apply KB.srun_refl].
   + intros y _. reflexivity.
 - destruct vs as [|v2 vs]; [discriminate|]. cbn in Lv. injection Lv as Lv.
   destruct (IH p2 i0 (tagged_env ((p, v1) :: r0) s) v2 vs K0 (with_cell s)
     (Cfg (Ret (VLam p2 (lamc ps i0) (tagged_env ((p, v1) :: r0) s))) (KApply (v2 :: vs) :: K0) (with_cell s)) Lv eq_refl)
     as (env & n & S1 & Eq).
   exists env, (S n). split.
   + eapply KB.srun_tau; [rewrite E; reflexivity|]. eapply KB.srun_tau; [reflexivity|]. exact S1.
   + intros y Ny. rewrite (Eq y Ny). unfold tagged_env.
     change (rev (p :: p2 :: ps)) with (rev (p2 :: ps) ++ [p]).
     change (rev (v1 :: v2 :: vs)) with (rev (v2 :: vs) ++ [v1]).
     rewrite combine_app by (rewrite !length_rev; cbn; rewrite Lv; reflexivity).
     rewrite <- app_assoc. cbn [combine app]. apply lookup_app_id. exact Ny.
Qed.

Lemma EnvRel_binds : forall j w G r0 rho ns vs0 vs, List.length ns = List.length vs0 -> Forall2 (VRel j w) vs0 vs ->
 EnvRel (VRel j) w G r0 rho -> EnvRel (VRel j) w (ns ++ G) (combine ns vs0 ++ r0) (combine ns vs ++ rho).
Proof.
 intros j w G r0 rho ns. induction ns as [|x ns IH]; intros vs0 vs L Fv H; [destruct vs0; [|discriminate]; inversion Fv; subst; exact H|].
 destruct vs0 as [|a0 vs0]; [discriminate|]. inversion Fv as [|? a ? vs' Ha Fr]; subst. cbn in L. injection L as L.
 cbn [app combine]. apply CC.env_cons; [apply IH; assumption|exact Ha].
Qed.

Lemma EnvRel_eqm : forall V w G E1 E2 r, (forall y, In y G -> y <> id_key) -> eqm E1 E2 -> EnvRel V w G E2 r -> EnvRel V w G E1 r.
Proof.
 intros V w G E1 E2 r N Eq H. eapply EnvRel_lookup; [|intros; reflexivity|exact H].
 intros y Iy. apply Eq. apply N. exact Iy.
Qed.

Lemma in_map_fst_combine : forall {A B} (l1 : list A) (l2 : list B) y, In y (map fst (combine l1 l2)) -> In y l1.
Proof.
 intros A B l1 l2 y I. apply in_map_iff in I as ([a b] & <- & I). exact (in_combine_l _ _ _ _ I).
Qed.

Lemma next_ELet : forall rho x a b K s, next_r R P (Cfg (Eval rho (ELet x a b)) K s) = MTau (Cfg (Eval rho a) (KLet x b rho :: K) s).
Proof. reflexivity. Qed.

Section LamSite.
Variables (rho0 rho : lenv) (p : name) (ps : list name) (i0 : expr) (r0 : lenv) (gl : list name) (inner : expr).
Hypothesis Hinner : forall j w' E0 E, K.wf_world w' -> EnvRel (VRel j) w' ((p :: ps) ++ gl) E0 E -> ERel j w' E0 i0 E inner.
Hypothesis Hid : ~ In id_key ((p :: ps) ++ gl).

Definition ArgRel (j : nat) (w : K.world) (a0 a : expr) : Prop :=
 forall j' w' ext, (j' <= j)%nat -> K.wext w w' -> (forall y, In y (map fst ext) -> In y (p :: ps)) ->
  ERel j' w' rho0 a0 (ext ++ rho) a.

Lemma ArgRel_mono : forall j j' w w' a0 a, (j' <= j)%nat -> K.wext w w' -> ArgRel j w a0 a -> ArgRel j' w' a0 a.
Proof.
 intros j j' w w' a0 a L W H j2 w2 ext L2 W2 Hy. apply H; [lia|eapply KB.wext_trans; eauto|exact Hy].
Qed.

Lemma lam_krel : forall qs rest0 rest q dn done0 done_t j w K0 K,
 p :: ps = rev dn ++ q :: qs -> List.length dn = List.length done0 -> Forall2 (VRel j w) done0 done_t ->
 List.length qs = List.length rest0 -> Forall2 (ArgRel j w) rest0 rest ->
 KRel j w K0 K -> EnvRel (VRel j) w gl r0 rho ->
 KRel j w (KArgs (VLam p (lamc ps i0) r0) done0 rest0 rho0 :: K0) (KLet q (lets qs rest inner) (combine dn done_t ++ rho) :: K).
Proof.
 induction qs as [|q' qs IH]; intros rest0 rest q dn done0 done_t j w K0 K HL Ld Hd Lq Ha HK HE;
  (apply (KB.ret_frame_tau sealed D); [exact HK|reflexivity|reflexivity| |intros; eexists; apply KB.next_KLet]);
  intros j' w' v0 v s0 s c1 L W HV HS E; rewrite KB.next_KLet in E; injection E as <-.
 - destruct rest0 as [|a0 rest0]; [|discriminate]. inversion Ha; subst. cbn [lets].
   assert (Lp : List.length (p :: ps) = S (List.length done0)) by (rewrite HL, length_app, length_rev; cbn; lia).
   destruct (rev (v0 :: done0)) as [|v1 vs] eqn:Er.
   { apply (f_equal (@List.length value)) in Er. rewrite length_rev in Er. discriminate. }
   assert (Lv : List.length vs = List.length ps).
   { apply (f_equal (@List.length value)) in Er. rewrite length_rev in Er. cbn in Er, Lp. lia. }
   destruct (apply_chain ps p i0 r0 v1 vs K0 s0 (Cfg (Ret v0) (KArgs (VLam p (lamc ps i0) r0) done0 [] rho0 :: K0) s0) Lv)
     as (env & n & S1 & Eq); [cbn [next_r ctl kont mem]; rewrite <- Er; reflexivity|].
   exists (Cfg (Eval env i0) K0 (cells n s0)). split; [exact S1|].
   assert (Rp : rev (p :: ps) = q :: dn) by (rewrite HL, rev_app_distr, rev_involutive; reflexivity).
   assert (Rv : rev (v1 :: vs) = v0 :: done0) by (rewrite <- Er, rev_involutive; reflexivity).
   rewrite Rp, Rv in Eq.
   eapply KB.ERel_apply; [|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply Hinner; [exact (KB.SRel_wf sealed D _ _ _ _ HS)|].
     eapply EnvRel_eqm; [|exact Eq|].
     { intros y Iy Ey. subst y. apply Hid. eapply in_app_or in Iy as [Iy|Iy]; apply in_or_app; [left|right]; exact Iy. }
     apply (EnvRel_incl _ _ _ ((q :: dn) ++ gl)).
     { intros y Iy. apply in_app_or in Iy as [Iy|Iy]; apply in_or_app; [left|right; exact Iy].
       rewrite HL in Iy. apply in_app_or in Iy as [Iy|Iy]; [right; apply (proj2 (in_rev dn y)); exact Iy|].
       destruct Iy as [<-|[]]; left; reflexivity. }
     change ((q, v) :: combine dn done_t ++ rho) with (combine (q :: dn) (v :: done_t) ++ rho).
     apply EnvRel_binds; [cbn; rewrite Ld; reflexivity| |].
     * constructor; [eapply KB.VRel_down; [|exact HV]; lia|]. eapply KB.Forall2_VRel_mono; [|exact W|exact Hd]. lia.
     * eapply KB.EnvRel_mono; [|exact W|exact HE]. lia.
   + eapply KB.KRel_mono; [|exact W|exact HK]. lia.
   + apply SRel_cells. eapply KB.SRel_down; [|exact HS]. lia.
 - destruct rest0 as [|a0 rest0]; [discriminate|]. inversion Ha as [|? a' ? rest' Ha1 Har]; subst. cbn [lets].
   cbn in Lq. injection Lq as Lq.
   exists (Cfg (Eval rho0 a0) (KArgs (VLam p (lamc ps i0) r0) (v0 :: done0) rest0 rho0 :: K0) s0).
   split; [eapply KB.srun_tau; [apply KB.next_KArgs_cons|apply KB.srun_refl]|].
   destruct j' as [|j2]; [apply KB.ObsT_0|].
   apply KB.ObsT_running; [reflexivity|exact I| | |].
   + intros x. cbn [kont mem]. eapply KB.ObsT_anti; [eapply KB.srun_tau; [apply KB.throw_frame_next; reflexivity|apply KB.srun_refl]|].
     apply (KB.KRel_throw sealed D); [eapply KB.KRel_mono; [|exact W|exact HK]; lia|eapply KB.SRel_down; [|exact HS]; lia].
   + intros c2 E2. rewrite next_ELet in E2. injection E2 as <-. eexists; split; [apply KB.srun_refl|].
     eapply KB.ERel_apply; [|apply le_n|eapply KB.wext_self; exact HS| |].
     * apply (Ha1 j2 w' ((q, v) :: combine dn done_t)); [lia|exact W|].
       intros y [<-|Iy]; rewrite HL; apply in_or_app; [right; left; reflexivity|left; apply (proj1 (in_rev dn y))].
       exact (in_map_fst_combine _ _ _ Iy).
     * apply (IH rest0 rest' q' (q :: dn) (v0 :: done0) (v :: done_t) j2 w' K0 K).
       -- rewrite HL. cbn [rev]. rewrite <- app_assoc. reflexivity.
       -- cbn. rewrite Ld. reflexivity.
       -- constructor; [eapply KB.VRel_down; [|exact HV]; lia|]. eapply KB.Forall2_VRel_mono; [|exact W|exact Hd]. lia.
       -- exact Lq.
       -- eapply Forall2_impl; [|exact Har]. intros b0 b Hb. eapply ArgRel_mono; [|exact W|exact Hb]. lia.
       -- eapply KB.KRel_mono; [|exact W|exact HK]. lia.
       -- eapply KB.EnvRel_mono; [|exact W|exact HE]. lia.
     * eapply KB.SRel_down; [|exact HS]. lia.
   + intros q2 kk r E2. rewrite next_ELet in E2. discriminate.
Qed.

Lemma ERel_lam_site : forall k w x A1 As A1' As', lookup x rho0 = Some (VLam p (lamc ps i0) r0) ->
 List.length As = List.length ps -> EnvRel (VRel k) w gl r0 rho -> Forall2 (ArgRel k w) (A1 :: As) (A1' :: As') ->
 ERel k w rho0 (EApp (EVar x) (A1 :: As)) rho (ELet p A1' (lets ps As' inner)).
Proof.
 intros k w x A1 As A1' As' Lx LA HE Ha. inversion Ha as [|? ? ? ? Ha1 Har]; subst.
 apply (KB.ERel_iff sealed D). intros j L w' W K0 K HK s0 s HS.
 eapply KB.ObsT_anti.
 { eapply KB.srun_tau; [reflexivity|]. eapply KB.srun_tau; [apply KB.sval_next; exact Lx|].
   eapply KB.srun_tau; [apply KB.next_KHead_cons|apply KB.srun_refl]. }
 destruct j as [|j]; [apply KB.ObsT_0|].
 apply KB.ObsT_running; [reflexivity|exact I| | |].
 - intros x'. cbn [kont mem]. eapply KB.ObsT_anti; [eapply KB.srun_tau; [apply KB.throw_frame_next; reflexivity|apply KB.srun_refl]|].
   apply (KB.KRel_throw sealed D); [eapply KB.KRel_down; [|exact HK]; lia|eapply KB.SRel_down; [|exact HS]; lia].
 - intros c2 E2. rewrite next_ELet in E2. injection E2 as <-. eexists; split; [apply KB.srun_refl|].
   eapply KB.ERel_apply; [|apply le_n|eapply KB.wext_self; exact HS| |].
   + apply (Ha1 j w' []); [lia|exact W|intros y []].
   + apply (lam_krel ps As As' p [] [] [] j w' K0 K); [reflexivity|reflexivity|constructor|symmetry; exact LA| | |].
     * eapply Forall2_impl; [|exact Har]. intros b0 b Hb. eapply ArgRel_mono; [|exact W|exact Hb]. lia.
     * eapply KB.KRel_down; [|exact HK]. lia.
     * eapply KB.EnvRel_mono; [|exact W|exact HE]. lia.
   + eapply KB.SRel_down; [|exact HS]. lia.
 - intros q2 kk r E2. rewrite next_ELet in E2. discriminate.
Qed.
End LamSite.

Lemma KRefF_lamsite : forall F g x p ps i0 gl A1 As A1' As' inner, In (KL x p ps i0 gl) F -> List.length As = List.length ps ->
 Forall2 (KRefF (dropl (p :: ps) F) (reml (p :: ps) g)) (A1 :: As) (A1' :: As') -> KRef ((p :: ps) ++ gl) i0 inner ->
 KRefF F g (EApp (EVar x) (A1 :: As)) (lets (p :: ps) (A1' :: As') inner).
Proof.
 intros F g x p ps i0 gl A1 As A1' As' inner I LA Ha Hi k w rho0 rho W HE HI.
 destruct (HI _ I) as (_ & Ngl & Nps & r0 & Lx & HE'). cbn [lets].
 apply (ERel_lam_site rho0 rho p ps i0 r0 gl inner); [| |exact Lx|exact LA|exact HE'|].
 - intros j w' E0 E W' H. apply Hi; assumption.
 - intros Iid. apply in_app_or in Iid as [Iid|Iid]; [exact (Nps Iid)|exact (Ngl Iid)].
 - eapply Forall2_impl; [|exact Ha]. intros a0 a H j' w' ext L W' Hy. apply H; [exact (proj2 W')| |].
   + eapply EnvRel_lookup; [intros; reflexivity| |].
     * intros y Iy. apply lookup_app_notin. intros Iy'. apply In_reml in Iy as [_ N]. exact (N (Hy y Iy')).
     * eapply EnvRel_incl; [intros y Iy; apply In_reml in Iy; exact (proj1 Iy)|]. eapply KB.EnvRel_mono; [exact L|exact W'|exact HE].
   + apply Inv_tgt_app; [exact Hy|]. eapply Inv_mono; [exact L|exact W'|exact HI].
Qed.

(* ---------- bound-now under a known frozen closure ---------- *)
(* The source's last argument is the known closure's name, X: it reads X (a value, no new cell)
   and enters the callee's body. Against the expansion's last let. *)
Lemma KRel_ca_lastvar : forall k w f ps eB done0 X vf rho0 x n rho K0 K,
 In (f, FUser ps eB) D -> List.length ps = S (S (List.length done0)) -> lookup X rho0 = Some vf ->
 KRel k w K0 K ->
 (forall j w' v0 v, (j <= k)%nat -> K.wext w w' -> VRel j w' v0 v ->
    ERel j w' (combine ps (rev (vf :: v0 :: done0))) eB ((x, v) :: rho) n) ->
 KRel k w (KCallArgs f done0 [EVar X] rho0 :: K0) (KLet x n rho :: K).
Proof.
 intros k w f ps eB done0 X vf rho0 x n rho K0 K Id Lp LX HK H.
 apply KB.ret_frame_tau; [exact HK|reflexivity|reflexivity| |intros v s; eexists; apply KB.next_KLet].
 intros j w' v0 v s0 s c1 L W HV HS E. rewrite KB.next_KLet in E. injection E as <-.
 assert (Hs0 : K.StoreHas D s0) by (destruct HS as (_ & H0 & _); exact H0).
 eexists; split.
 - eapply KB.srun_tau; [apply KB.next_KCallArgs_cons|].
   eapply KB.srun_tau; [apply KB.sval_next; exact LX|].
   eapply KB.srun_tau; [|apply KB.srun_refl].
   rewrite PL.next_ca_call. apply KB.call_named_user; [exact (Hs0 f _ Id)|rewrite PL.len_rev', Lp; reflexivity].
 - eapply KB.ERel_apply.
   + apply (H j w' v0 v); [lia|exact W|eapply KB.VRel_down; [|exact HV]; lia].
   + apply le_n.
   + eapply KB.wext_self; exact HS.
   + eapply KB.KRel_mono; [|exact W|exact HK]; lia.
   + eapply KB.SRel_down; [|exact HS]; lia.
Qed.

(* (shen.bind! X0 Y0 B0 X), X a known frozen closure KF X E0 gl, against bound-now's expansion
   (let a1 X' (let a2 Y' (let a3 B' N))) with E copied in: the same proof as
   JitFrontProlog.bind_rule_sound, except that the frozen argument is the closure X names, whose
   captured environment the entry relates on gl to the target's at the call. So JitFrontProlog's
   beq_sound applies with that environment and gl as its scope, and each copied place is checked
   against E0 in KRef (premise HTK). The arguments are checked with the entries the earlier lets
   may shadow dropped. *)
Lemma KRefF_bindsite : forall F g X ex0 gl x0 y0 b0 a1 x a2 y a3 b n p1 p2 p3 p4 eB v1 v2 (tk : expr -> bool),
 K.D_wf sealed D -> In (KF X ex0 gl) F ->
 lookup FD.bind_name D = Some (FUser [p1; p2; p3; p4] eB) -> lookup PL.do_name D = Some (FUser [v1; v2] (EVar v2)) ->
 v1 <> v2 -> p1 <> p2 -> p1 <> p3 -> p1 <> p4 -> p2 <> p3 -> p2 <> p4 -> p3 <> p4 -> p4 <> id_key ->
 FD.binder_ok p1 a1 = true -> FD.binder_ok p2 a2 = true -> FD.binder_ok p3 a3 = true ->
 ~ In a1 g -> ~ In a2 g -> ~ In a3 g ->
 KRefF F g x0 x -> KRefF (dropl [a1] F) g y0 y -> KRefF (dropl [a2; a1] F) g b0 b ->
 (forall e', tk e' = true -> KRef (PL.gfv gl e') ex0 e') ->
 PL.beq (S (FD.dsize eB)) tk p4 [(p3, a3); (p2, a2); (p1, a1)] eB n = true ->
 KRefF F g (ECall FD.bind_name [x0; y0; b0; EVar X]) (ELet a1 x (ELet a2 y (ELet a3 b n))).
Proof.
 intros F g X ex0 gl x0 y0 b0 a1 x a2 y a3 b n p1 p2 p3 p4 eB v1 v2 tk Dw IX LB LD V12 D12 D13 D14 D23 D24 D34 P4
   B1 B2 B3 N1 N2 N3 Kx Ky Kb HTK Bq.
 destruct (PL.binder_ok_ne _ _ B1) as [Np1 Na1]. destruct (PL.binder_ok_ne _ _ B2) as [Np2 Na2].
 destruct (PL.binder_ok_ne _ _ B3) as [Np3 Na3].
 pose proof (PL.lookup_some_In _ _ _ LB) as IB. pose proof (PL.lookup_some_In _ _ _ LD) as ID.
 intros k w rho0 rho Ww HEnv HI.
 destruct (HI _ IX) as (_ & _ & r0 & LX & HE').
 apply (KB.ERel_push sealed D k w rho0 _ rho _ rho0 x0 rho x
   (fun K0 => KCallArgs FD.bind_name [] [y0; b0; EVar X] rho0 :: K0) (fun K => KLet a1 (ELet a2 y (ELet a3 b n)) rho :: K)).
 - intros; reflexivity.
 - intros; reflexivity.
 - intros j1 w1 K0 K L1 W1 HK. apply (PL.KRel_ca_let sealed D); [exact HK|]. intros j2 w2 vx0 vx L2 W2 HV2.
   assert (W12 : K.wext w w2) by (eapply KB.wext_trans; [exact W1|exact W2]).
   split.
   + apply Ky; [exact (proj2 W2)| |].
     * apply (PL.EnvRel_notin sealed D); [exact N1|]. eapply KB.EnvRel_mono; [|exact W12|exact HEnv]. lia.
     * change ((a1, vx) :: rho) with ([(a1, vx)] ++ rho). apply Inv_tgt_app; [intros y' [<-|[]]; left; reflexivity|].
       eapply Inv_mono; [|exact W12|exact HI]. lia.
   + apply (PL.KRel_ca_let sealed D); [eapply KB.KRel_mono; [exact L2|exact W2|exact HK]|]. intros j3 w3 vy0 vy L3 W3 HV3.
     assert (W13 : K.wext w w3) by (eapply KB.wext_trans; [exact W12|exact W3]).
     split.
     * apply Kb; [exact (proj2 W3)| |].
       -- apply (PL.EnvRel_notin sealed D); [exact N2|]. apply (PL.EnvRel_notin sealed D); [exact N1|].
          eapply KB.EnvRel_mono; [|exact W13|exact HEnv]. lia.
       -- change ((a2, vy) :: (a1, vx) :: rho) with ([(a2, vy); (a1, vx)] ++ rho).
          apply Inv_tgt_app; [intros y' [<-|[<-|[]]]; [left|right; left]; reflexivity|].
          eapply Inv_mono; [|exact W13|exact HI]. lia.
     * apply (KRel_ca_lastvar _ _ FD.bind_name [p1; p2; p3; p4] eB [vy0; vx0] X (VFrozen ex0 r0));
        [exact IB|reflexivity|exact LX|eapply KB.KRel_mono; [|exact W3|eapply KB.KRel_mono; [exact L2|exact W2|exact HK]]; lia|].
       intros j4 w4 vb0 vb L4 W4 HV4. cbn [rev app combine].
       assert (W14 : K.wext w w4) by (eapply KB.wext_trans; [exact W13|exact W4]).
       apply (PL.beq_sound sealed D Dw tk p4 ex0 r0 rho gl j4 w4)
         with (v1 := v1) (v2 := v2) (fuel := S (FD.dsize eB)) (rn := [(p3, a3); (p2, a2); (p1, a1)]).
       -- exact HTK.
       -- intros x' Ix _. destruct (HE' x' Ix) as (u0 & u & E0 & E & U).
          exists u0, u. split; [exact E0|split; [exact E|eapply KB.VRel_mono; [|exact W14|exact U]; lia]].
       -- exact P4.
       -- exact ID.
       -- exact V12.
       -- exact Bq.
       -- split; [apply le_n|]. split; [apply KG.wext_refl; exact (proj2 W4)|]. split; [|split; [|split]].
          ++ intros x' y' Ix Fr V. cbn [FD.var_ok] in V. unfold FD.free_in in Fr. cbn [existsb fst] in Fr.
             destruct (text_eqb p3 x') eqn:E3.
             ** apply text_eqb_eq in E3. apply text_eqb_eq in V. subst x' y'. exists vb0, vb.
                rewrite (PL.lookup_cons_ne p3 p1), (PL.lookup_cons_ne p3 p2), PL.lookup_cons_eq by congruence.
                rewrite PL.lookup_cons_eq. split; [reflexivity|split; [reflexivity|exact HV4]].
             ** destruct (text_eqb a3 y') eqn:F3; [discriminate|]. destruct (text_eqb p2 x') eqn:E2.
                --- apply text_eqb_eq in E2. apply text_eqb_eq in V. subst x' y'. exists vy0, vy.
                    rewrite (PL.lookup_cons_ne p2 p1), PL.lookup_cons_eq by congruence.
                    rewrite (PL.lookup_cons_ne a2 a3) by (apply PL.text_eqb_false in F3; congruence). rewrite PL.lookup_cons_eq.
                    split; [reflexivity|split; [reflexivity|eapply KB.VRel_mono; [|exact W4|exact HV3]; lia]].
                --- destruct (text_eqb a2 y') eqn:F2; [discriminate|]. destruct (text_eqb p1 x') eqn:E1.
                    +++ apply text_eqb_eq in E1. apply text_eqb_eq in V. subst x' y'. exists vx0, vx.
                        rewrite PL.lookup_cons_eq.
                        rewrite (PL.lookup_cons_ne a1 a3) by (apply PL.text_eqb_false in F3; congruence).
                        rewrite (PL.lookup_cons_ne a1 a2) by (apply PL.text_eqb_false in F2; congruence). rewrite PL.lookup_cons_eq.
                        split; [reflexivity|split; [reflexivity|]].
                        eapply KB.VRel_mono; [|eapply KB.wext_trans; [exact W3|exact W4]|exact HV2]; lia.
                    +++ discriminate.
          ++ intros Ip Fp. rewrite (PL.lookup_cons_ne p4 p1), (PL.lookup_cons_ne p4 p2), (PL.lookup_cons_ne p4 p3) by congruence.
             rewrite PL.lookup_cons_eq. reflexivity.
          ++ intros z Iz Hz Nz. unfold FD.hidden in Hz. cbn [existsb snd] in Hz. rewrite orb_false_r in Hz.
             apply orb_false_iff in Hz as [Z3 Hz]. apply orb_false_iff in Hz as [Z2 Z1].
             apply PL.text_eqb_false in Z1, Z2, Z3.
             rewrite (PL.lookup_cons_ne z a3), (PL.lookup_cons_ne z a2), (PL.lookup_cons_ne z a1) by congruence. reflexivity.
          ++ intros a' b' [E|[E|[E|[]]]]; injection E as <- <-; split; assumption.
 - intros j1 w1 L1 W1. apply Kx; [exact (proj2 W1)| |].
   + eapply KB.EnvRel_mono; [|exact W1|exact HEnv]. lia.
   + eapply Inv_mono; [|exact W1|exact HI]. lia.
Qed.
End Rel.
(* ======================= the checker ======================= *)
Definition is_thaw_body (d : fundef) : bool := match d with
 | FUser [v] (EApp (EVar v') []) => text_eqb v v' | _ => false end.

Fixpoint find_kf (x : name) (F : list kc) : option (expr * list name) := match F with
 | [] => None
 | KF y e0 gl :: F => if text_eqb x y then Some (e0, gl) else find_kf x F
 | _ :: F => find_kf x F end.

Fixpoint find_kl (x : name) (F : list kc) : option (name * list name * expr * list name) := match F with
 | [] => None
 | KL y p ps i0 gl :: F => if text_eqb x y then Some (p, ps, i0, gl) else find_kl x F
 | _ :: F => find_kl x F end.

(* lower.shen's lambda-params and lambda-body. *)
Fixpoint lam_split (b : expr) : list name * expr := match b with
 | ELam p b => let (ps, i) := lam_split b in (p :: ps, i)
 | _ => ([], b) end.

Fixpoint unlets (xs : list name) (e : expr) : option (list expr * expr) := match xs with
 | [] => Some ([], e)
 | x :: xs => match e with
   | ELet y v b => if text_eqb x y then match unlets xs b with Some (vs, i) => Some (v :: vs, i) | None => None end else None
   | _ => None end end.

Definition subl (a b : list name) : bool := forallb (fun y => memb y b) a.

(* A further site rule the copy checker may be given (the bind-site rule of let-frozen copying,
   for one), with its soundness as a premise of cc_sound. *)
Definition Hook : Type := list kc -> list name -> expr -> expr -> bool.
Definition no_hook : Hook := fun _ _ _ _ => false.

Section Checker.
Variables (hook : Hook) (D : list (name * fundef)).

(* One node, the same head constructor, with the parts by `rec`: a binder drops the entries it
   would shadow. *)
Definition cc_same (rec : list kc -> list name -> expr -> expr -> bool) (F : list kc) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | EVar x, EVar y => bound g x && text_eqb x y
 | ELam x b0, ELam y b => text_eqb x y && rec (drop x F) (x :: g) b0 b
 | ELet x a0 b0, ELet y a b => text_eqb x y && rec F g a0 a && rec (drop x F) (x :: g) b0 b
 | EIf c0 a0 b0, EIf c a b => rec F g c0 c && rec F g a0 a && rec F g b0 b
 | EAnd a0 b0, EAnd a b | EOr a0 b0, EOr a b | ETrap a0 b0, ETrap a b => rec F g a0 a && rec F g b0 b
 | ECond cl0, ECond cl => forall2b (fun p0 p => rec F g (fst p0) (fst p) && rec F g (snd p0) (snd p)) cl0 cl
 | EFreeze b0, EFreeze b | EType b0, EType b => rec F g b0 b
 | EApp h0 as0, EApp h as1 => rec F g h0 h && forall2b (rec F g) as0 as1
 | ECall f as0, ECall f' as1 => text_eqb f f' && forall2b (rec F g) as0 as1
 | _, _ => lit_eqb e0 e end.

(* A thaw of a known frozen closure, as (X) or as (thaw X) with the kernel's thaw in D: the
   target has a copy of the closure body, checked against it in the closure's scope. *)
Definition cc_thaw (rec : list kc -> list name -> expr -> expr -> bool) (F : list kc) (e0 e : expr) : bool :=
 match e0 with
 | EApp (EVar x) [] => match find_kf x F with Some (b0, gl) => rec [] gl b0 e | None => false end
 | ECall f [EVar x] => text_eqb f FD.thaw_name && d_has D FD.thaw_name is_thaw_body &&
     match find_kf x F with Some (b0, gl) => rec [] gl b0 e | None => false end
 | _ => false end.

(* A known lambda applied to all its parameters: the target binds them in order to the
   arguments, then runs the body. The arguments are checked in a scope without the parameters. *)
Definition cc_lam (rec : list kc -> list name -> expr -> expr -> bool) (F : list kc) (g : list name) (e0 e : expr) : bool :=
 match e0 with
 | EApp (EVar x) (a1 :: as0) => match find_kl x F with
   | Some (p, ps, i0, gl) => Nat.eqb (List.length as0) (List.length ps) &&
       match unlets (p :: ps) e with
       | Some (as1, inner) => forall2b (rec (dropl (p :: ps) F) (reml (p :: ps) g)) (a1 :: as0) as1 &&
                              rec [] ((p :: ps) ++ gl) i0 inner
       | None => false end
   | None => false end
 | _ => false end.

(* The let that the target dropped: X is a known closure in the body, out of the scope. *)
Definition cc_intro (rec : list kc -> list name -> expr -> expr -> bool) (F : list kc) (g : list name) (e0 e : expr) : bool :=
 match e0 with
 | ELet x (EFreeze b0) body0 =>
     negb (text_eqb x id_key) && negb (memb id_key (K.fv b0)) && subl (K.fv b0) g &&
     rec (KF x b0 (K.fv b0) :: drop x F) (rem x g) body0 e
 | ELet x (ELam p b) body0 => let (ps, i0) := lam_split b in
     negb (text_eqb x id_key) && negb (memb id_key (K.fv (ELam p b))) && negb (memb id_key (p :: ps)) &&
     subl (K.fv (ELam p b)) g && rec (KL x p ps i0 (K.fv (ELam p b)) :: drop x F) (rem x g) body0 e
 | _ => false end.

(* bound-now under a known frozen closure: (shen.bind! X0 Y0 B0 X), X a known frozen closure,
   against bound-now's expansion with the closure's body copied in. JitFrontProlog.bind_rule's
   checks, with the frozen body E0 and its scope gl from the entry: each copied place is checked
   against E0 in the scope of its free names in gl, with no entries. *)
Definition cc_bind (rec : list kc -> list name -> expr -> expr -> bool) (F : list kc) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | ECall f [x0; y0; b0; EVar X], ELet a1 x (ELet a2 y (ELet a3 b n)) =>
   text_eqb f FD.bind_name &&
   match find_kf X F, lookup FD.bind_name D, lookup PL.do_name D with
   | Some (ex0, gl), Some (FUser [p1; p2; p3; p4] eB), Some (FUser [v1; v2] (EVar v2')) =>
     negb (text_eqb v1 v2) && text_eqb v2 v2' &&
     nodupb [p1; p2; p3; p4] && negb (text_eqb p4 id_key) &&
     FD.binder_ok p1 a1 && FD.binder_ok p2 a2 && FD.binder_ok p3 a3 && FD.disjoint [a1; a2; a3] g &&
     rec F g x0 x && rec (dropl [a1] F) g y0 y && rec (dropl [a2; a1] F) g b0 b &&
     PL.beq (S (FD.dsize eB)) (fun e' => rec [] (PL.gfv gl e') ex0 e') p4 [(p3, a3); (p2, a2); (p1, a1)] eB n
   | _, _, _ => false end
 | _, _ => false end.

Fixpoint cc (n : nat) (F : list kc) (g : list name) (e0 e : expr) {struct n} : bool :=
 match n with
 | O => false
 | S n => cf_chk D n g e0 e || hook F g e0 e || cc_thaw (cc n) F e0 e || cc_lam (cc n) F g e0 e ||
          cc_intro (cc n) F g e0 e || cc_bind (cc n) F g e0 e || cc_same (cc n) F g e0 e end.
End Checker.

Lemma find_kf_In : forall x F b0 gl, find_kf x F = Some (b0, gl) -> In (KF x b0 gl) F.
Proof.
 intros x F. induction F as [|[y e0 gl'|y p ps i0 gl'] F IH]; intros b0 gl H; cbn in H; try discriminate.
 - destruct (text_eqb x y) eqn:E; [|right; apply IH; exact H].
   apply text_eqb_eq in E. subst. injection H as <- <-. left. reflexivity.
 - right. apply IH. exact H.
Qed.

Lemma find_kl_In : forall x F p ps i0 gl, find_kl x F = Some (p, ps, i0, gl) -> In (KL x p ps i0 gl) F.
Proof.
 intros x F. induction F as [|[y e0 gl'|y p' ps' i0' gl'] F IH]; intros p ps i0 gl H; cbn in H; try discriminate.
 - right. apply IH. exact H.
 - destruct (text_eqb x y) eqn:E; [|right; apply IH; exact H].
   apply text_eqb_eq in E. subst. injection H as <- <- <- <-. left. reflexivity.
Qed.

Lemma lam_split_eq : forall b ps i0, lam_split b = (ps, i0) -> b = lamc ps i0.
Proof.
 induction b; intros ps i0 H; cbn in H; try (injection H as <- <-; reflexivity).
 destruct (lam_split b) as [ps' i'] eqn:E. injection H as <- <-. cbn. f_equal. apply IHb. reflexivity.
Qed.

Lemma unlets_sound : forall xs e vs i, unlets xs e = Some (vs, i) -> e = lets xs vs i /\ List.length vs = List.length xs.
Proof.
 induction xs as [|x xs IH]; intros e vs i H; cbn in H; [injection H as <- <-; split; reflexivity|].
 destruct e; try discriminate. destruct (text_eqb x x0) eqn:E; [|discriminate]. apply text_eqb_eq in E. subst x0.
 destruct (unlets xs e2) as [[vs' i']|] eqn:U; [|discriminate]. injection H as <- <-.
 destruct (IH _ _ _ U) as [-> L]. split; [reflexivity|cbn; rewrite L; reflexivity].
Qed.

Lemma subl_incl : forall a b, subl a b = true -> incl a b.
Proof. intros a b H y I. unfold subl in H. rewrite forallb_forall in H. apply memb_In. apply H. exact I. Qed.

Lemma thaw_d_has : forall D, d_has D FD.thaw_name is_thaw_body = true -> exists v, In (FD.thaw_name, FUser [v] (EApp (EVar v) [])) D.
Proof.
 intros D H. destruct (d_has_in _ _ _ H) as (d & I & T).
 destruct d as [|ps b]; cbn in T; try discriminate.
 destruct ps as [|v [|]]; try discriminate. destruct b; try discriminate. destruct b; try discriminate.
 destruct args; try discriminate. apply text_eqb_eq in T. subst. eexists. exact I.
Qed.

Section CSound.
Variables (sealed : list name) (D : list (name * fundef)) (hook : Hook).
Notation KRefF := (KRefF sealed D).
Hypotheses (FG : K.fund_gen_statement sealed D) (PC : K.prim_compat_statement sealed D) (Dw : K.D_wf sealed D)
 (HCF : forall n g e0 e, cf_chk D n g e0 e = true -> K.KRef sealed D g e0 e)
 (Hhook : forall F g e0 e, hook F g e0 e = true -> KRefF F g e0 e).

Lemma Forall2_rec : forall (rec : list kc -> list name -> expr -> expr -> bool) F g l0 l,
 (forall F g a b, rec F g a b = true -> KRefF F g a b) -> forall2b (rec F g) l0 l = true -> Forall2 (KRefF F g) l0 l.
Proof. intros rec F g l0 l Hr H. eapply forall2b_sound; [|exact H]. intros a b E. apply Hr. exact E. Qed.

Lemma cc_same_sound : forall (rec : list kc -> list name -> expr -> expr -> bool),
 (forall F g a b, rec F g a b = true -> KRefF F g a b) ->
 forall F g e0 e, cc_same rec F g e0 e = true -> KRefF F g e0 e.
Proof.
 intros rec Hr F g e0 e H.
 destruct e0; destruct e; cbn [cc_same] in H;
 repeat match goal with E : (_ && _)%bool = true |- _ => apply andb_true_iff in E as [? ?] end;
 repeat match goal with E : text_eqb _ _ = true |- _ => apply text_eqb_eq in E; subst end;
 first
 [ discriminate
 | apply lit_eqb_sound in H as [<- [v Hv]]; apply KRefF_of_KRef; exact (CC.compat_lit sealed D g _ v Hv)
 | cbn [lit_eqb] in H; discriminate
 | apply KRefF_of_KRef; exact (CC.compat_lit sealed D g ENil VNil eq_refl)
 | apply KRefF_of_KRef; apply CC.compat_var; apply JitKRefFv.JitKRefFv.bound_In; assumption
 | apply KRefF_lam; apply Hr; assumption
 | apply KRefF_let; apply Hr; assumption
 | apply KRefF_if; apply Hr; assumption
 | apply KRefF_and; apply Hr; assumption
 | apply KRefF_or; apply Hr; assumption
 | apply (KRefF_trap sealed D FG PC Dw); apply Hr; assumption
 | apply KRefF_frz; apply Hr; assumption
 | apply KRefF_type; apply Hr; assumption
 | apply KRefF_cond; eapply forall2b_sound; [|exact H]; intros p0 p E; apply andb_true_iff in E as [E1 E2];
   split; apply Hr; assumption
 | apply (KRefF_app sealed D FG PC Dw); [apply Hr; assumption|eapply Forall2_rec; eassumption]
 | apply (KRefF_call sealed D FG PC Dw); eapply Forall2_rec; eassumption ].
Qed.

Lemma cc_thaw_sound : forall (rec : list kc -> list name -> expr -> expr -> bool),
 (forall F g a b, rec F g a b = true -> KRefF F g a b) ->
 forall F g e0 e, cc_thaw D rec F e0 e = true -> KRefF F g e0 e.
Proof.
 intros rec Hr F g e0 e H. unfold cc_thaw in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|b h|b|b|f ps b|h args|f args]; try discriminate.
 - destruct h; try discriminate. destruct args; try discriminate.
   destruct (find_kf x F) as [[b0 gl]|] eqn:Ef; [|discriminate].
   eapply KRefF_thaw; [apply find_kf_In; exact Ef|]. apply KRefF_nil. apply Hr. exact H.
 - destruct args as [|a [|a2 l]]; try discriminate; [|destruct a; discriminate]. destruct a; try discriminate.
   apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2]. apply text_eqb_eq in H1. subst f.
   destruct (thaw_d_has D H2) as [v Iv].
   destruct (find_kf x F) as [[b0 gl]|] eqn:Ef; [|discriminate].
   eapply KRefF_thaw_call; [exact Iv|apply find_kf_In; exact Ef|]. apply KRefF_nil. apply Hr. exact H3.
Qed.

Lemma cc_lam_sound : forall (rec : list kc -> list name -> expr -> expr -> bool),
 (forall F g a b, rec F g a b = true -> KRefF F g a b) ->
 forall F g e0 e, cc_lam rec F g e0 e = true -> KRefF F g e0 e.
Proof.
 intros rec Hr F g e0 e H. unfold cc_lam in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|b h|b|b|f ps b|h args|f args]; try discriminate. destruct h; try discriminate. destruct args as [|a1 as0]; [discriminate|].
 destruct (find_kl x F) as [[[[p ps] i0] gl]|] eqn:Ef; [|discriminate].
 apply andb_true_iff in H as [L H]. apply Nat.eqb_eq in L.
 destruct (unlets (p :: ps) e) as [[as1 inner]|] eqn:U; [|discriminate].
 apply andb_true_iff in H as [Ha Hi]. destruct (unlets_sound _ _ _ _ U) as [-> Lu].
 pose proof (Forall2_rec rec _ _ _ _ Hr Ha) as Fa. destruct as1 as [|a1' as1]; [inversion Fa|].
 eapply KRefF_lamsite; [apply find_kl_In; exact Ef|exact L|exact Fa|]. apply KRefF_nil. apply Hr. exact Hi.
Qed.

Lemma cc_intro_sound : forall (rec : list kc -> list name -> expr -> expr -> bool),
 (forall F g a b, rec F g a b = true -> KRefF F g a b) ->
 forall F g e0 e, cc_intro rec F g e0 e = true -> KRefF F g e0 e.
Proof.
 intros rec Hr F g e0 e H. unfold cc_intro in H.
 destruct e0 as [n|t|s|b| |x|x b|x a b|c a b|a b|a b|cl|b h|b|b|f ps b|h args|f args]; try discriminate. destruct a as [n|t|s|bb| |y|p lb|y a lb|c a lb|a lb|a lb|cl|lb h|fb|lb|f ps lb|h args|f args]; try discriminate.
 - destruct (lam_split lb) as [ps i0] eqn:Es.
   repeat match goal with E : (_ && _)%bool = true |- _ => apply andb_true_iff in E as [? ?] end.
   repeat match goal with E : negb _ = true |- _ => apply negb_true_iff in E end.
   rewrite (lam_split_eq _ _ _ Es) in *.
   apply KRefF_letlam with (gl := K.fv (ELam p (lamc ps i0))).
   + intros E. subst. rewrite text_eqb_refl in *. discriminate.
   + apply memb_false. assumption.
   + apply memb_false. assumption.
   + apply subl_incl. assumption.
   + apply Hr. assumption.
 - repeat match goal with E : (_ && _)%bool = true |- _ => apply andb_true_iff in E as [? ?] end.
   repeat match goal with E : negb _ = true |- _ => apply negb_true_iff in E end.
   apply KRefF_letfrz with (gl := K.fv fb).
   + intros E. subst. rewrite text_eqb_refl in *. discriminate.
   + apply memb_false. assumption.
   + apply subl_incl. assumption.
   + apply Hr. assumption.
Qed.

Lemma cc_bind_sound : forall (rec : list kc -> list name -> expr -> expr -> bool),
 (forall F g a b, rec F g a b = true -> KRefF F g a b) ->
 forall F g e0 e, cc_bind D rec F g e0 e = true -> KRefF F g e0 e.
Proof.
 intros rec Hr F g e0 e H. unfold cc_bind in H.
 destruct e0 as [| | | | | | | | | | | | | | | | |f args]; try discriminate H.
 destruct args as [|x0 [|y0 [|b0 [|xv [|a5 l5]]]]]; try discriminate H;
  try (destruct xv; discriminate H).
 destruct xv as [| | | | |X| | | | | | | | | | | |]; try discriminate H.
 destruct e as [| | | | | | |a1 x e1| | | | | | | | | |]; try discriminate H.
 destruct e1 as [| | | | | | |a2 y e2| | | | | | | | | |]; try discriminate H.
 destruct e2 as [| | | | | | |a3 b n| | | | | | | | | |]; try discriminate H.
 apply andb_true_iff in H as [Ef H]. apply text_eqb_eq in Ef. subst f.
 destruct (find_kf X F) as [[ex0 gl]|] eqn:EK; [|discriminate H].
 destruct (lookup FD.bind_name D) as [[q|ps eB]|] eqn:LB; try discriminate H.
 destruct ps as [|p1 [|p2 [|p3 [|p4 [|]]]]]; try discriminate H.
 destruct (lookup PL.do_name D) as [[q|vs ed]|] eqn:LD; try discriminate H.
 destruct vs as [|v1 [|v2 [|]]]; try discriminate H.
 destruct ed as [| | | | |v2'| | | | | | | | | | | |]; try discriminate H.
 repeat (apply andb_true_iff in H as [H ?]).
 match goal with E : text_eqb v2 v2' = true |- _ => apply text_eqb_eq in E; subst v2' end.
 match goal with E : negb (text_eqb v1 v2) = true |- _ => apply negb_true_iff, PL.text_eqb_false in E end.
 match goal with E : negb (text_eqb p4 id_key) = true |- _ => apply negb_true_iff, PL.text_eqb_false in E end.
 match goal with ND : nodupb [p1; p2; p3; p4] = true |- _ =>
   cbn [nodupb bound existsb] in ND; rewrite !orb_false_r in ND;
   repeat (apply andb_true_iff in ND as [? ND]) end.
 rewrite !negb_orb in *.
 repeat match goal with Hn : (negb _ && _)%bool = true |- _ => apply andb_true_iff in Hn as [? ?] end.
 repeat match goal with Hn : negb (text_eqb _ _) = true |- _ => apply negb_true_iff in Hn; apply PL.text_eqb_false in Hn end.
 match goal with Dj : FD.disjoint [a1; a2; a3] g = true |- _ =>
   unfold FD.disjoint in Dj; cbn [forallb] in Dj; rewrite andb_true_r in Dj;
   apply andb_true_iff in Dj as [G1 Dj]; apply andb_true_iff in Dj as [G2 G3];
   apply negb_true_iff in G1, G2, G3 end.
 eapply (KRefF_bindsite sealed D F g X ex0 gl x0 y0 b0 a1 x a2 y a3 b n p1 p2 p3 p4 eB v1 v2
   (fun e' => rec [] (PL.gfv gl e') ex0 e')); try eassumption; try congruence.
 - apply find_kf_In. exact EK.
 - intros I. apply PL.bound_iff in I. congruence.
 - intros I. apply PL.bound_iff in I. congruence.
 - intros I. apply PL.bound_iff in I. congruence.
 - apply Hr. assumption.
 - apply Hr. assumption.
 - apply Hr. assumption.
 - intros e' T. apply KRefF_nil. apply Hr. exact T.
Qed.

Theorem cc_sound_hyp : forall n F g e0 e, cc hook D n F g e0 e = true -> KRefF F g e0 e.
Proof.
 induction n as [|n IH]; intros F g e0 e H; cbn [cc] in H; [discriminate|].
 repeat match goal with E : (_ || _)%bool = true |- _ => apply orb_true_iff in E as [E|E] end.
 - apply KRefF_of_KRef. eapply HCF. exact H.
 - apply Hhook. exact H.
 - eapply cc_thaw_sound; [exact IH|exact H].
 - eapply cc_lam_sound; [exact IH|exact H].
 - eapply cc_intro_sound; [exact IH|exact H].
 - eapply cc_bind_sound; [exact IH|exact H].
 - eapply cc_same_sound; [exact IH|exact H].
Qed.
End CSound.

(* Instantiated: the fundamental property (JitKRefFund.fund_gen), the primitives' compatibility
   (JitKRefPrim.prim_compat) and cf_chk's soundness (cf_chk_sound) discharge the Section
   hypotheses. What remains: D_wf, and the hook's own soundness. *)
Theorem cc_sound : forall sealed D hook, K.D_wf sealed D ->
 (forall F g e0 e, hook F g e0 e = true -> KRefF sealed D F g e0 e) ->
 forall n g e0 e, cc hook D n [] g e0 e = true -> K.KRef sealed D g e0 e.
Proof.
 intros sealed D hook Dw Hh n g e0 e H. apply KRefF_nil.
 eapply (cc_sound_hyp sealed D hook (JitKRefFund.JitKRefFund.fund_gen sealed D)
   (JitKRefPrim.JitKRefPrim.prim_compat sealed D) Dw (cf_chk_sound sealed D Dw) Hh). exact H.
Qed.

(* With no further site rule: D_wf is the only premise. *)
Corollary copy_chk_sound : forall sealed D, K.D_wf sealed D ->
 forall n g e0 e, cc no_hook D n [] g e0 e = true -> K.KRef sealed D g e0 e.
Proof.
 intros sealed D Dw. apply cc_sound; [exact Dw|]. intros F g e0 e H. discriminate.
Qed.
(* ======================= fold-arith needs a store fact ======================= *)
(* KRef asks nothing of the store beyond StoreHas D, so with D = [] a store may define + as a user
   function. There (+ 1 2) returns 1 while the folded 3 returns 3: no fold of + is a KRef
   refinement without (+, FPrim PAdd) in D, or another store fact for +. *)
Definition fx_x : name := of_string "x".
Definition fx_y : name := of_string "y".
Definition fx_one : expr := ENum (NInt 1).
Definition fx_two : expr := ENum (NInt 2).
Definition fx_src : expr := ECall plus_name [fx_one; fx_two].
Definition fx_tgt : expr := ENum (NInt 3).
Definition fx_s : store := Store [] [] [(plus_name, FUser [fx_x; fx_y] (EVar fx_x))].
Definition fx_k1 : frame := KCallArgs plus_name [] [fx_two] [].
Definition fx_k2 : frame := KCallArgs plus_name [VNum (NInt 1)] [] [].
Definition fx_det : list config :=
 [Cfg (Eval [] fx_src) [] fx_s; Cfg (Eval [] fx_one) [fx_k1] fx_s; Cfg (Ret (VNum (NInt 1))) [fx_k1] fx_s;
  Cfg (Eval [] fx_two) [fx_k2] fx_s; Cfg (Ret (VNum (NInt 2))) [fx_k2] fx_s;
  Cfg (Eval [(fx_x, VNum (NInt 1)); (fx_y, VNum (NInt 2))] (EVar fx_x)) [] fx_s; Cfg (Ret (VNum (NInt 1))) [] fx_s].

Section Fx.
Variable sealed : list name.
Notation R := (jit_rules sealed).
Notation P := jit_profile.

Definition fx_inv (c : config) : Prop :=
 In c fx_det \/ exists x, (exists r, resource_exn R r = Some x) /\
   In c [Cfg (Throw x) [fx_k1] fx_s; Cfg (Throw x) [fx_k2] fx_s; Cfg (Throw x) [] fx_s].

Lemma fx_inv_step : forall c l c1, step_r R P c l c1 -> fx_inv c -> fx_inv c1.
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

Lemma fx_inv_star : forall c t c', star (step_r R P) c t c' -> fx_inv c -> fx_inv c'.
Proof. intros c t c' H. induction H as [|c l c1 t c2 St _ IH]; intros I; [exact I|apply IH; exact (fx_inv_step _ _ _ St I)]. Qed.

Lemma fx_tgt_runs : K.runs sealed 1 (Cfg (Eval [] fx_tgt) [] fx_s) [] (Cfg (Ret (VNum (NInt 3))) [] fx_s).
Proof. eapply ux_runs_tau; [reflexivity|]. constructor. Qed.

Theorem fold_arith_needs_store : ~ K.KRef sealed [] [] fx_src fx_tgt.
Proof.
 intros H.
 assert (W0 : K.wf_world []) by (split; constructor).
 assert (HE : K.EnvRel_with (K.VRel sealed [] 5) [] [] [] []) by (intros y []).
 pose proof (H 5%nat [] [] [] W0 HE) as E.
 assert (HK : K.KRel sealed [] 5 [] [] []) by exact (KG.KRel_top sealed [] 5 [] W0).
 assert (HS : K.SRel sealed [] 5 [] fx_s fx_s).
 { assert (SH : K.StoreHas [] fx_s) by (intros f d []).
   unfold K.SRel, K.SRel_with.
   split; [exact W0|split; [exact SH|split; [exact SH|split; [reflexivity|split; [constructor|]]]]].
   intros l0 l []. }
 pose proof (E 5%nat (le_n _) [] (KG.wext_refl [] W0) [] [] HK fx_s fx_s HS) as O.
 destruct (O 1%nat [] _ ltac:(lia) fx_tgt_runs) as (A & _ & _).
 destruct (A _ _ eq_refl) as (v0 & s0 & w' & S0 & _ & G & _).
 destruct (fx_inv_star _ _ _ S0 (or_introl (or_introl eq_refl))) as [I|(x & _ & I)].
 - cbn in I. repeat destruct I as [Ec|I]; try discriminate; try contradiction.
   injection Ec; intros; subst. cbn in G. discriminate.
 - cbn in I. repeat destruct I as [Ec|I]; try discriminate; contradiction.
Qed.
End Fx.

(* ======================= tests of the copy checker (not evidence of anything general) ======================= *)
Definition t_g : name := of_string "G".
Definition t_f : name := of_string "F".
Definition t_a : name := of_string "A".
Definition t_c : name := of_string "C".
Definition t_p : name := of_string "X".
Definition t_q : name := of_string "Y".
Definition t_cons (a b : expr) : expr := ECall N.cons_name [a; b].
Definition t_frz_body : expr := t_cons (EVar t_a) ENil.
(* let-frozen copy: (let G (freeze (cons A ())) (if C (G) 0)) to (if C (cons A ()) 0). *)
Example cc_frz_copy : cc no_hook [] 20 [] [t_a; t_c]
 (ELet t_g (EFreeze t_frz_body) (EIf (EVar t_c) (EApp (EVar t_g) []) (ENum (NInt 0))))
 (EIf (EVar t_c) t_frz_body (ENum (NInt 0))) = true.
Proof. vm_compute. reflexivity. Qed.
(* ... with (thaw G), given the kernel's thaw in D ... *)
Definition t_thaw_D : list (name * fundef) := [(FD.thaw_name, FUser [of_string "V"] (EApp (EVar (of_string "V")) []))].
Example cc_frz_copy_thaw : cc no_hook t_thaw_D 20 [] [t_a; t_c]
 (ELet t_g (EFreeze t_frz_body) (EIf (EVar t_c) (ECall FD.thaw_name [EVar t_g]) (ENum (NInt 0))))
 (EIf (EVar t_c) t_frz_body (ENum (NInt 0))) = true.
Proof. vm_compute. reflexivity. Qed.
(* ... but not without it ... *)
Example cc_frz_copy_thaw_noD : cc no_hook [] 20 [] [t_a; t_c]
 (ELet t_g (EFreeze t_frz_body) (EIf (EVar t_c) (ECall FD.thaw_name [EVar t_g]) (ENum (NInt 0))))
 (EIf (EVar t_c) t_frz_body (ENum (NInt 0))) = false.
Proof. vm_compute. reflexivity. Qed.
(* ... nor when a binder between captures a free name of the body ... *)
Example cc_frz_capture : cc no_hook [] 20 [] [t_a; t_c]
 (ELet t_g (EFreeze t_frz_body) (ELet t_a (ENum (NInt 5)) (EApp (EVar t_g) [])))
 (ELet t_a (ENum (NInt 5)) t_frz_body) = false.
Proof. vm_compute. reflexivity. Qed.
(* ... nor when the body uses G other than by thawing it. *)
Example cc_frz_escape : cc no_hook [] 20 [] [t_a; t_c; t_g]
 (ELet t_g (EFreeze t_frz_body) (EVar t_g)) (EVar t_g) = false.
Proof. vm_compute. reflexivity. Qed.
(* let-lambda: (let F (lambda X (lambda Y (cons X Y))) (cons (F 1 2) (F A 4))) to
   (cons (let X 1 (let Y 2 (cons X Y))) (let X A (let Y 4 (cons X Y)))). *)
Definition t_inner : expr := t_cons (EVar t_p) (EVar t_q).
Example cc_lam_copy : cc no_hook [] 20 [] [t_a]
 (ELet t_f (ELam t_p (ELam t_q t_inner))
   (t_cons (EApp (EVar t_f) [ENum (NInt 1); ENum (NInt 2)]) (EApp (EVar t_f) [EVar t_a; ENum (NInt 4)])))
 (t_cons (ELet t_p (ENum (NInt 1)) (ELet t_q (ENum (NInt 2)) t_inner))
         (ELet t_p (EVar t_a) (ELet t_q (ENum (NInt 4)) t_inner))) = true.
Proof. vm_compute. reflexivity. Qed.
(* Rejected: a use with fewer arguments than parameters ... *)
Example cc_lam_partial : cc no_hook [] 20 [] [t_a]
 (ELet t_f (ELam t_p (ELam t_q t_inner)) (EApp (EVar t_f) [ENum (NInt 1)]))
 (ELet t_p (ENum (NInt 1)) (ELam t_q t_inner)) = false.
Proof. vm_compute. reflexivity. Qed.
(* ... and an argument that names a parameter (the target evaluates it under the earlier lets). *)
Example cc_lam_arg_param : cc no_hook [] 20 [] [t_p]
 (ELet t_f (ELam t_p (ELam t_q t_inner)) (EApp (EVar t_f) [ENum (NInt 1); EVar t_p]))
 (ELet t_p (ENum (NInt 1)) (ELet t_q (EVar t_p) t_inner)) = false.
Proof. vm_compute. reflexivity. Qed.
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
(* bound-now under a let-bound freeze: shen.bind! here only thaws its fourth parameter. *)
Definition t_P (i : string) : name := of_string i.
Definition t_bind_D : list (name * fundef) :=
 [(FD.bind_name, FUser [t_P "P1"; t_P "P2"; t_P "P3"; t_P "P4"] (EApp (EVar (t_P "P4")) []));
  (PL.do_name, FUser [t_P "V1"; t_P "V2"] (EVar (t_P "V2")))].
Definition t_bind_src (b : expr) : expr :=
 ELet t_g (EFreeze t_frz_body) (ECall FD.bind_name [fx_one; fx_two; ENil; EVar t_g]).
Definition t_bind_tgt (a1 : name) (b : expr) : expr :=
 ELet a1 fx_one (ELet (t_P "Q2") fx_two (ELet (t_P "Q3") ENil b)).
Example cc_bind_copy : cc no_hook t_bind_D 20 [] [t_a] (t_bind_src t_frz_body) (t_bind_tgt (t_P "Q1") t_frz_body) = true.
Proof. vm_compute. reflexivity. Qed.
Example cc_bind_wrong_body : cc no_hook t_bind_D 20 [] [t_a] (t_bind_src t_frz_body) (t_bind_tgt (t_P "Q1") (EVar t_a)) = false.
Proof. vm_compute. reflexivity. Qed.
Example cc_bind_shadow : cc no_hook t_bind_D 20 [] [t_a] (t_bind_src t_frz_body) (t_bind_tgt t_a t_frz_body) = false.
Proof. vm_compute. reflexivity. Qed.

(* ---------- where uncurrying would fire in stage 0 (a TEST harness, not proof) ---------- *)
(* Run by stage0_to_rocq.py --uncurry over the 955 parsed stage 0 sources: the dynamic
   applications with two or more arguments (EApp with a head of any shape), the only source shape
   norm-apply rewrites to a curried chain, and among them those with a trailing argument that is
   not a literal or a variable (where the evaluation order also changes). For each: (definitions
   with one, sites). *)
Definition is_multi_app (e : expr) : bool := match e with EApp _ (_ :: _ :: _) => true | _ => false end.
Definition is_atomic (e : expr) : bool := match e with
 | ENum _ | EStr _ | ESym _ | EBool _ | ENil | EVar _ => true | _ => false end.
Definition is_multi_app_nonatomic (e : expr) : bool := match e with
 | EApp _ (_ :: rest) => negb (forallb is_atomic rest) && Nat.leb 1 (List.length rest) | _ => false end.
Definition uncurry_scan (fs : list JitLowerStage0.JitLowerStage0.sx) : list (string * (nat * nat)) :=
 let bs := PL.src_bodies fs in
 [("bodies", (List.length bs, List.length fs));
  ("multi_app", PL.shape_count is_multi_app bs);
  ("multi_app_nonatomic", PL.shape_count is_multi_app_nonatomic bs)]%string.
Example uncurry_scan_sees : is_multi_app ux_src = true.
Proof. reflexivity. Qed.

End JitFrontCopyFold.
