(* Shen/JIT Phase 2, the front checkers' framework (F00).
   A front pass (share, norm) is validated per definition by a Rocq checker of the pair (source,
   witness). Every such checker is an instance of one function, `fchk`, parameterised by a list of
   rewrite rules; its soundness (`fchk_sound`) is proved once, here, from KRef's compatibility
   lemmas, and each rule only has to prove its own `rule_sound`.

   fchk rules fuel g e0 e tries, in order:
   1. syntactic equality, with `scoped g e` (the case KRef_refl_statement covers);
   2. the same head constructor on both sides, recursing into the parts, the scope extended for
      ELet and ELam (the compat_* statements);
   3. each rule in turn, given `fchk rules (fuel - 1)` as its recursive checker `rec`.
   All three recurse at fuel - 1, so the definition is structural in the fuel.

   Composition contract. A rule may rewrite the SOURCE side at the current node to an intermediate
   e0' and call `rec g e0' e` on the SAME target node; a following rule can then fire on e0'
   inside that call, so stacked rewrites at one position chain without any transitivity of KRef
   (which does not hold in general for a step-indexed relation). Extra TARGET steps (share's
   thaw) are paid from the step index inside the rule's own soundness proof.

   `rule_sound r`: for every `rec` sound at every index (rec g a b = true implies KRef g a b, and
   KRef quantifies over every index k), every (g, e0, e) that r accepts is in KRef. The intended
   proof shape: the source steps from e0 to e0' by source-only steps (JitKRefBase.ERel_anti and its
   instances), then rec's soundness.

   FrontHyps bundles D_wf, KRef_refl, KRef_scope, the ERel anti-reduction lemma and every compat_*
   statement of JitKRef.v. It is a Section hypothesis, never an axiom: kref-fund's front_hyps is
   to discharge it. KRef_scope and the anti-reduction lemma are already proved in JitKRefBase
   (front_scope_proved, front_anti_proved below), so only D_wf, KRef_refl and the compat_*
   statements remain for kref-fund.

   Proved here (each Theorem in Audit_Jit, "Closed under the global context"): expr_eqb_eq,
   front_scope_proved, front_anti_proved, same_sound and fchk_sound (FrontHyps and Forall
   rule_sound are their premises once the Section closes).
   Does NOT prove: any compat_* statement, KRef_refl, or any rule's soundness. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerPrim JitLowerStep JitLowerThm JitLowerCheck JitKRef JitKRefGround JitKRefBase.
Import ListNotations.
Set Warnings "-notation-for-abbreviation".
Module JitFrontCheck.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort
 JitProfile.JitProfile JitLowerRel.JitLowerRel JitKRef.JitKRef.

(* ---------- syntactic equality of expressions ---------- *)
Definition num_eqb (a b : num) : bool := match a, b with
 | NInt x, NInt y => Z.eqb x y | NFloat x, NFloat y => N.eqb x y | _, _ => false end.

Fixpoint forall2b {A B} (f : A -> B -> bool) (l0 : list A) (l : list B) : bool := match l0, l with
 | [], [] => true
 | a :: l0, b :: l => f a b && forall2b f l0 l
 | _, _ => false end.

Fixpoint expr_eqb (a b : expr) {struct a} : bool := match a, b with
 | ENum x, ENum y => num_eqb x y
 | EStr x, EStr y => text_eqb x y
 | ESym x, ESym y => text_eqb x y
 | EBool x, EBool y => Bool.eqb x y
 | ENil, ENil => true
 | EVar x, EVar y => text_eqb x y
 | ELam x a, ELam y b => text_eqb x y && expr_eqb a b
 | ELet x a1 a2, ELet y b1 b2 => text_eqb x y && expr_eqb a1 b1 && expr_eqb a2 b2
 | EIf a1 a2 a3, EIf b1 b2 b3 => expr_eqb a1 b1 && expr_eqb a2 b2 && expr_eqb a3 b3
 | EAnd a1 a2, EAnd b1 b2 | EOr a1 a2, EOr b1 b2 | ETrap a1 a2, ETrap b1 b2 =>
     expr_eqb a1 b1 && expr_eqb a2 b2
 | ECond l0, ECond l => (fix go (l0 : list (expr * expr)) (l : list (expr * expr)) : bool :=
     match l0, l with
     | [], [] => true
     | (c0, d0) :: l0, (c, d) :: l => expr_eqb c0 c && expr_eqb d0 d && go l0 l
     | _, _ => false end) l0 l
 | EFreeze a, EFreeze b | EType a, EType b => expr_eqb a b
 | EDefun f ps a, EDefun g qs b => text_eqb f g && forall2b text_eqb ps qs && expr_eqb a b
 | EApp h0 l0, EApp h l => expr_eqb h0 h && (fix go (l0 l : list expr) : bool := match l0, l with
     | [], [] => true | x :: l0, y :: l => expr_eqb x y && go l0 l | _, _ => false end) l0 l
 | ECall f l0, ECall g l => text_eqb f g && (fix go (l0 l : list expr) : bool := match l0, l with
     | [], [] => true | x :: l0, y :: l => expr_eqb x y && go l0 l | _, _ => false end) l0 l
 | _, _ => false end.

(* An induction principle that sees the expressions inside ECond, EApp and ECall. *)
Section ExprInd.
Variable Q : expr -> Prop.
Hypotheses
 (H_num : forall n, Q (ENum n)) (H_str : forall t, Q (EStr t)) (H_sym : forall s, Q (ESym s))
 (H_bool : forall b, Q (EBool b)) (H_nil : Q ENil) (H_var : forall x, Q (EVar x))
 (H_lam : forall x b, Q b -> Q (ELam x b))
 (H_let : forall x a b, Q a -> Q b -> Q (ELet x a b))
 (H_if : forall c a b, Q c -> Q a -> Q b -> Q (EIf c a b))
 (H_and : forall a b, Q a -> Q b -> Q (EAnd a b)) (H_or : forall a b, Q a -> Q b -> Q (EOr a b))
 (H_cond : forall l, Forall (fun p => Q (fst p) /\ Q (snd p)) l -> Q (ECond l))
 (H_trap : forall a b, Q a -> Q b -> Q (ETrap a b))
 (H_freeze : forall b, Q b -> Q (EFreeze b)) (H_type : forall b, Q b -> Q (EType b))
 (H_defun : forall f ps b, Q b -> Q (EDefun f ps b))
 (H_app : forall h l, Q h -> Forall Q l -> Q (EApp h l))
 (H_call : forall f l, Forall Q l -> Q (ECall f l)).
Fixpoint expr_ind' (e : expr) : Q e :=
 let fix all (l : list expr) : Forall Q l := match l with
   | [] => @Forall_nil expr Q | a :: l => @Forall_cons expr Q a l (expr_ind' a) (all l) end in
 let fix allp (l : list (expr * expr)) : Forall (fun p => Q (fst p) /\ Q (snd p)) l := match l with
   | [] => @Forall_nil (expr * expr) (fun p => Q (fst p) /\ Q (snd p))
   | (c, d) :: l => @Forall_cons _ (fun p => Q (fst p) /\ Q (snd p)) (c, d) l (conj (expr_ind' c) (expr_ind' d)) (allp l) end in
 match e with
 | ENum n => H_num n | EStr t => H_str t | ESym s => H_sym s | EBool b => H_bool b | ENil => H_nil
 | EVar x => H_var x | ELam x b => H_lam x b (expr_ind' b)
 | ELet x a b => H_let x a b (expr_ind' a) (expr_ind' b)
 | EIf c a b => H_if c a b (expr_ind' c) (expr_ind' a) (expr_ind' b)
 | EAnd a b => H_and a b (expr_ind' a) (expr_ind' b) | EOr a b => H_or a b (expr_ind' a) (expr_ind' b)
 | ECond l => H_cond l (allp l) | ETrap a b => H_trap a b (expr_ind' a) (expr_ind' b)
 | EFreeze b => H_freeze b (expr_ind' b) | EType b => H_type b (expr_ind' b)
 | EDefun f ps b => H_defun f ps b (expr_ind' b)
 | EApp h l => H_app h l (expr_ind' h) (all l) | ECall f l => H_call f l (all l) end.
End ExprInd.

Lemma num_eqb_eq : forall a b, num_eqb a b = true -> a = b.
Proof.
 intros [x|x] [y|y] H; cbn in H; try discriminate.
 - apply Z.eqb_eq in H; subst; reflexivity.
 - apply N.eqb_eq in H; subst; reflexivity.
Qed.

Lemma forall2b_sound : forall {A B} (f : A -> B -> bool) (Q : A -> B -> Prop) l0 l,
 (forall a b, In a l0 -> f a b = true -> Q a b) -> forall2b f l0 l = true -> Forall2 Q l0 l.
Proof.
 intros A B f Q l0. induction l0 as [|a l0 IH]; intros [|b l] H E; cbn in E; try discriminate.
 - constructor.
 - apply andb_true_iff in E as [E1 E2]. constructor.
   + apply H; [left; reflexivity|exact E1].
   + apply IH; [intros a' b' I; apply H; right; exact I|exact E2].
Qed.

Lemma text_list_eq : forall ps qs, forall2b text_eqb ps qs = true -> ps = qs.
Proof.
 induction ps as [|p ps IH]; intros [|q qs] E; cbn in E; try discriminate; [reflexivity|].
 apply andb_true_iff in E as [E1 E2]. apply text_eqb_eq in E1. rewrite E1, (IH qs E2). reflexivity.
Qed.

Theorem expr_eqb_eq : forall a b, expr_eqb a b = true -> a = b.
Proof.
 induction a using expr_ind'; intros b' E; destruct b'; cbn in E; try discriminate;
  repeat match goal with
  | E : _ && _ = true |- _ => apply andb_true_iff in E as [? ?]
  | E : text_eqb _ _ = true |- _ => apply text_eqb_eq in E; subst
  | E : num_eqb _ _ = true |- _ => apply num_eqb_eq in E; subst
  | E : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in E; subst
  | E : forall2b text_eqb _ _ = true |- _ => apply text_list_eq in E; subst
  end; try reflexivity; try (f_equal; auto; fail).
 all: lazymatch goal with
 | |- ECond _ = ECond _ =>
   f_equal;
   match goal with E : (fix go (l0 l1 : list (expr * expr)) {struct l0} : bool := _) ?m0 ?m1 = true,
                   H : Forall _ ?m0 |- _ => revert E; clear -H; revert m1 end;
   match goal with H : Forall _ _ |- _ => induction H as [|p l [Hc Hd] F IH] end;
   [|destruct p as [c d]; cbn [fst snd] in Hc, Hd];
   intros [|[c' d'] l'] E; cbn in E; try discriminate; [reflexivity|];
   apply andb_true_iff in E as [E E3]; apply andb_true_iff in E as [E1 E2];
   rewrite (Hc _ E1), (Hd _ E2), (IH _ E3); reflexivity
 | |- EApp _ _ = EApp _ _ =>
   match goal with IHh : forall b, expr_eqb ?h b = true -> ?h = b, Eh : expr_eqb ?h ?h' = true |- _ =>
     rewrite (IHh _ Eh) end; f_equal;
   match goal with E : (fix go (l0 l1 : list expr) {struct l0} : bool := _) ?m0 ?m1 = true,
                   H : Forall _ ?m0 |- _ => revert E; clear -H; revert m1 end;
   match goal with H : Forall _ _ |- _ => induction H as [|x l Hx F IH] end;
   intros [|y l'] E; cbn in E; try discriminate; [reflexivity|];
   apply andb_true_iff in E as [E1 E2]; rewrite (Hx _ E1), (IH _ E2); reflexivity
 | |- ECall _ _ = ECall _ _ =>
   f_equal;
   match goal with E : (fix go (l0 l1 : list expr) {struct l0} : bool := _) ?m0 ?m1 = true,
                   H : Forall _ ?m0 |- _ => revert E; clear -H; revert m1 end;
   match goal with H : Forall _ _ |- _ => induction H as [|x l Hx F IH] end;
   intros [|y l'] E; cbn in E; try discriminate; [reflexivity|];
   apply andb_true_iff in E as [E1 E2]; rewrite (Hx _ E1), (IH _ E2); reflexivity
 end.
Qed.

(* ---------- rules and the checker ---------- *)
(* A rule: given the recursive checker (at one fuel less), a scope and a pair, accept or not. *)
Definition rule := (list name -> expr -> expr -> bool) -> list name -> expr -> expr -> bool.

(* The same head constructor on both sides, the parts checked by rec. EDefun and the literals
   and variables have no case: equality (step 1) is their only route. *)
Definition same (rec : list name -> expr -> expr -> bool) (g : list name) (e0 e : expr) : bool :=
 match e0, e with
 | ELam x0 b0, ELam x b => text_eqb x0 x && rec (x :: g) b0 b
 | ELet x0 a0 b0, ELet x a b => text_eqb x0 x && rec g a0 a && rec (x :: g) b0 b
 | EIf c0 a0 b0, EIf c a b => rec g c0 c && rec g a0 a && rec g b0 b
 | EAnd a0 b0, EAnd a b => rec g a0 a && rec g b0 b
 | EOr a0 b0, EOr a b => rec g a0 a && rec g b0 b
 | ETrap a0 b0, ETrap a b => rec g a0 a && rec g b0 b
 | ECond l0, ECond l => forall2b (fun p0 p => rec g (fst p0) (fst p) && rec g (snd p0) (snd p)) l0 l
 | EFreeze b0, EFreeze b => rec g b0 b
 | EType b0, EType b => rec g b0 b
 | EApp h0 l0, EApp h l => rec g h0 h && forall2b (rec g) l0 l
 | ECall f0 l0, ECall f l => text_eqb f0 f && forall2b (rec g) l0 l
 | _, _ => false end.

Fixpoint fchk (rules : list rule) (fuel : nat) (g : list name) (e0 e : expr) {struct fuel} : bool :=
 match fuel with
 | O => false
 | S f => (expr_eqb e0 e && scoped g e)
          || same (fchk rules f) g e0 e
          || existsb (fun r => r (fchk rules f) g e0 e) rules
 end.

Section Front.
Variables (sealed : list name) (D : list (name * fundef)).
Notation R := (jit_rules sealed).
Notation P := jit_profile.
Notation srun := (JitKRef.JitKRef.srun sealed).
Notation SRel := (JitKRef.JitKRef.SRel sealed D).
Notation ERel := (JitKRef.JitKRef.ERel sealed D).
Notation KRef := (JitKRef.JitKRef.KRef sealed D).
Notation D_wf := (JitKRef.JitKRef.D_wf sealed D).
Notation KRef_refl_statement := (JitKRef.JitKRef.KRef_refl_statement sealed D).
Notation KRef_scope_statement := (JitKRef.JitKRef.KRef_scope_statement sealed D).
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

(* JitKRefBase.ERel_anti, as a statement. *)
Definition ERel_anti_statement : Prop := forall k w rho0 e0 rho e,
 (forall j w' K0 s0 s, (j <= k)%nat -> wext w w' -> SRel j w' s0 s -> exists rho0' e0' s0',
    srun (Cfg (Eval rho0 e0) K0 s0) [] (Cfg (Eval rho0' e0') K0 s0') /\ SRel j w' s0' s /\ ERel j w' rho0' e0' rho e) ->
 ERel k w rho0 e0 rho e.

Record FrontHyps : Prop := {
 fh_D_wf : D_wf;
 fh_refl : KRef_refl_statement;
 fh_scope : KRef_scope_statement;
 fh_anti : ERel_anti_statement;
 fh_lit : compat_lit_statement;
 fh_var : compat_var_statement;
 fh_let : compat_let_statement;
 fh_if : compat_if_statement;
 fh_and : compat_and_statement;
 fh_or : compat_or_statement;
 fh_cond : compat_cond_statement;
 fh_type : compat_type_statement;
 fh_trap : compat_trap_statement;
 fh_lambda : compat_lambda_statement;
 fh_freeze : compat_freeze_statement;
 fh_call : compat_call_statement;
 fh_app : compat_app_statement;
 fh_defun : compat_defun_statement }.

(* The two fields already proved, so that kref-fund's front_hyps owes only the others. *)
Theorem front_scope_proved : KRef_scope_statement.
Proof. exact (JitKRefBase.JitKRefBase.KRef_scope sealed D). Qed.
Theorem front_anti_proved : ERel_anti_statement.
Proof. exact (JitKRefBase.JitKRefBase.ERel_anti sealed D). Qed.

(* A checker is sound when every pair it accepts is in KRef, at every scope. *)
Definition chk_sound (c : list name -> expr -> expr -> bool) : Prop :=
 forall g a b, c g a b = true -> KRef g a b.

Definition rule_sound (r : rule) : Prop :=
 forall rec, chk_sound rec -> forall g e0 e, r rec g e0 e = true -> KRef g e0 e.

Section Sound.
Hypothesis FH : FrontHyps.
Variable rules : list rule.
Hypothesis RS : Forall rule_sound rules.

Theorem same_sound : forall rec, chk_sound rec -> forall g e0 e, same rec g e0 e = true -> KRef g e0 e.
Proof.
 intros rec Hr g e0 e E. destruct e0, e; cbn in E; try discriminate;
  repeat match goal with
  | E : _ && _ = true |- _ => apply andb_true_iff in E as [? ?]
  | E : text_eqb _ _ = true |- _ => apply text_eqb_eq in E; subst
  end.
 - apply (fh_lambda FH). apply Hr; assumption.
 - apply (fh_let FH); apply Hr; assumption.
 - apply (fh_if FH); apply Hr; assumption.
 - apply (fh_and FH); apply Hr; assumption.
 - apply (fh_or FH); apply Hr; assumption.
 - apply (fh_cond FH). eapply forall2b_sound; [|exact E]. intros p0 p _ Ep.
   apply andb_true_iff in Ep as [E1 E2]. split; apply Hr; assumption.
 - apply (fh_trap FH); [exact (fh_D_wf FH)|apply Hr; assumption|apply Hr; assumption].
 - apply (fh_freeze FH). apply Hr; assumption.
 - apply (fh_type FH). apply Hr; assumption.
 - apply (fh_app FH); [exact (fh_D_wf FH)|apply Hr; assumption|].
   eapply forall2b_sound; [|eassumption]. intros a b _ Ea. apply Hr; exact Ea.
 - apply (fh_call FH); [exact (fh_D_wf FH)|].
   eapply forall2b_sound; [|eassumption]. intros a b _ Ea. apply Hr; exact Ea.
Qed.

Theorem fchk_sound : forall fuel, chk_sound (fchk rules fuel).
Proof.
 induction fuel as [|f IH]; intros g e0 e E; cbn in E; [discriminate|].
 apply orb_true_iff in E as [E|E]; [apply orb_true_iff in E as [E|E]|].
 - apply andb_true_iff in E as [E1 E2]. apply expr_eqb_eq in E1. subst e0.
   apply (fh_refl FH); [exact (fh_D_wf FH)|exact E2].
 - exact (same_sound _ IH g e0 e E).
 - apply existsb_exists in E as (r & I & Er).
   exact (proj1 (Forall_forall _ _) RS r I _ IH g e0 e Er).
Qed.
End Sound.
End Front.
End JitFrontCheck.
