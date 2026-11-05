(* E2E-06 item: the existing Rocq lexical fragment (Lambda.v) embeds in the
   KLambda small-step semantics. De Bruijn variables become level-named
   variables, Add becomes a named call of `+`, and every terminating outcome
   of the fuel interpreter (value or error) is reached by internal KLambda
   steps with the caller's continuation and store unchanged. Premises: the
   function namespace binds `+` to the primitive (redefinition would change the
   meaning), and the profile has no stack bound (Lambda.v has none). *)
From Coq Require Import List ZArith NArith String Bool Lia Relation_Operators.
From Buri Require Import Lambda Observation KLSyntax KLValue KLSemantics.
Import ListNotations.
Module KLBridge.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Module L := Lambda.Lexical.

Definition lvl (n : nat) : name := [N.of_nat n].
Definition unbound_name : name := [].
Definition plus_name : name := of_string "+".

Fixpoint tr (d : nat) (e : L.term) : expr := match e with
 | L.Lit z => ENum (NInt z)
 | L.Bool b => EBool b
 | L.Var i => if Nat.ltb i d then EVar (lvl (d - 1 - i)) else EVar unbound_name
 | L.Lam b => ELam (lvl d) (tr (S d) b)
 | L.App f a => EApp (tr d f) [tr d a]
 | L.LetIn a b => ELet (lvl d) (tr d a) (tr (S d) b)
 | L.If c a b => EIf (tr d c) (tr d a) (tr d b)
 | L.Add a b => ECall plus_name [tr d a; tr d b] end.

Fixpoint tr_val (v : L.value) : value := match v with
 | L.Int z => VNum (NInt z)
 | L.Boolean b => VBool b
 | L.Closure b env => VLam (lvl (List.length env)) (tr (S (List.length env)) b)
     ((fix go (env : list L.value) : lenv := match env with
       | [] => [] | w :: rest => (lvl (List.length rest), tr_val w) :: go rest end) env) end.
Fixpoint tr_env (env : list L.value) : lenv := match env with
 | [] => [] | w :: rest => (lvl (List.length rest), tr_val w) :: tr_env rest end.
Lemma tr_val_closure : forall b env,
 tr_val (L.Closure b env) = VLam (lvl (List.length env)) (tr (S (List.length env)) b) (tr_env env).
Proof. reflexivity. Qed.

Definition tr_err (e : L.error) : exn := match e with
 | L.Unbound => XUnboundVar unbound_name | L.NotCallable => XNotCallable
 | L.NotBoolean => XNotBoolean | L.NotInteger => XPrim PAdd end.
Definition tr_out (o : L.outcome) : control := match o with
 | L.Returned v => Ret (tr_val v) | L.Raised e => Throw (tr_err e) end.

Lemma lvl_eqb : forall n m, text_eqb (lvl n) (lvl m) = Nat.eqb n m.
Proof.
 intros; unfold lvl; cbn. rewrite andb_true_r.
 destruct (Nat.eqb n m) eqn:E.
 - apply Nat.eqb_eq in E; subst; apply N.eqb_refl.
 - apply N.eqb_neq; intro H; apply Nat.eqb_neq in E; apply E; apply Nat2N.inj; exact H.
Qed.

Lemma lookup_unbound : forall env, lookup unbound_name (tr_env env) = None.
Proof. induction env; cbn; auto. Qed.

Lemma lookup_level : forall env i v, nth_error env i = Some v ->
 lookup (lvl (List.length env - 1 - i)) (tr_env env) = Some (tr_val v).
Proof.
 induction env as [|w env IH]; intros i v H; [destruct i; discriminate|].
 cbn [tr_env lookup List.length]. destruct i as [|i]; cbn in H.
 - inversion H; subst. rewrite lvl_eqb. replace (S (List.length env) - 1 - 0) with (List.length env) by lia.
   rewrite Nat.eqb_refl; reflexivity.
 - pose proof (nth_error_Some env i) as Hs. assert (i < List.length env) by (apply Hs; congruence).
   rewrite lvl_eqb. replace (S (List.length env) - 1 - S i) with (List.length env - 1 - i) by lia.
   destruct (Nat.eqb (List.length env - 1 - i) (List.length env)) eqn:E; [apply Nat.eqb_eq in E; lia|].
   apply IH; exact H.
Qed.

Section Sim.
Variable P : profile.
Hypothesis unbounded : stack_limit P = None.

Definition tau := clos_refl_trans_1n config (fun a b => next P a = MTau b).
Lemma tau_step : forall a b c, next P a = MTau b -> tau b c -> tau a c.
Proof. intros; econstructor; eauto. Qed.
Lemma tau_trans : forall a b c, tau a b -> tau b c -> tau a c.
Proof. intros a b c H; induction H; intros K; [exact K|econstructor; [eassumption|apply IHclos_refl_trans_1n; exact K]]. Qed.

Lemma push_free : forall f k c s, push P f k c s = Cfg c (f :: k) s.
Proof. intros; unfold push; rewrite unbounded; reflexivity. Qed.

Lemma throw_unwind : forall x f k s, (forall h r, f <> KTrap h r) ->
 next P (Cfg (Throw x) (f :: k) s) = MTau (Cfg (Throw x) k s).
Proof. intros x f k s N; destruct f; try reflexivity. exfalso; eapply N; reflexivity. Qed.

Theorem embed : forall n env e r, L.eval n env e = Some r ->
 forall k s, lookup plus_name (gfuns s) = Some (FPrim PAdd) ->
 tau (Cfg (Eval (tr_env env) (tr (List.length env) e)) k s) (Cfg (tr_out r) k s).
Proof.
 induction n as [|n IH]; intros env e r H k s Plus; [discriminate|].
 destruct e; cbn [L.eval tr] in H |- *.
 - inversion H; subst. eapply tau_step; [reflexivity|constructor].
 - inversion H; subst. eapply tau_step; [reflexivity|constructor].
 - destruct (Nat.ltb n0 (List.length env)) eqn:Lt.
   + apply Nat.ltb_lt in Lt. destruct (nth_error env n0) eqn:E.
     * inversion H; subst. eapply tau_step; [|constructor].
       cbn. rewrite (lookup_level env n0 v E). reflexivity.
     * apply nth_error_None in E; lia.
   + apply Nat.ltb_ge in Lt. assert (nth_error env n0 = None) as E by (apply nth_error_None; lia).
     rewrite E in H; inversion H; subst. eapply tau_step; [|constructor].
     cbn. rewrite lookup_unbound. reflexivity.
 - inversion H; subst. eapply tau_step; [|constructor]. reflexivity.
 - (* application: function, argument, then call *)
   eapply tau_step; [cbn; rewrite push_free; reflexivity|].
   destruct (L.eval n env e1) as [[vf|ef]|] eqn:F; try discriminate.
   + eapply tau_trans; [exact (IH _ _ _ F _ _ Plus)|]. cbn [tr_out].
     eapply tau_step; [reflexivity|].
     destruct (L.eval n env e2) as [[va|ea]|] eqn:A; try discriminate.
     * eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|]. cbn [tr_out].
       destruct vf as [z|b|body captured].
       -- inversion H; subst. eapply tau_step; [reflexivity|constructor].
       -- inversion H; subst. eapply tau_step; [reflexivity|constructor].
       -- eapply tau_step; [reflexivity|]. cbn [rev app continue_with].
          change ((lvl (List.length captured), tr_val va) :: tr_env captured) with (tr_env (va :: captured)).
          exact (IH _ _ _ H _ _ Plus).
     * inversion H; subst. eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|].
       eapply tau_step; [reflexivity|constructor].
   + inversion H; subst. eapply tau_trans; [exact (IH _ _ _ F _ _ Plus)|].
     eapply tau_step; [reflexivity|constructor].
 - (* let *)
   eapply tau_step; [cbn; rewrite push_free; reflexivity|].
   destruct (L.eval n env e1) as [[va|ea]|] eqn:A; try discriminate.
   + eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|]. cbn [tr_out].
     eapply tau_step; [reflexivity|].
     change ((lvl (List.length env), tr_val va) :: tr_env env) with (tr_env (va :: env)).
     exact (IH _ _ _ H _ _ Plus).
   + inversion H; subst. eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|].
     eapply tau_step; [reflexivity|constructor].
 - (* if *)
   eapply tau_step; [cbn; rewrite push_free; reflexivity|].
   destruct (L.eval n env e1) as [[vc|ec]|] eqn:C; try discriminate.
   + eapply tau_trans; [exact (IH _ _ _ C _ _ Plus)|]. cbn [tr_out].
     destruct vc as [z|b|body captured].
     * inversion H; subst. eapply tau_step; [reflexivity|constructor].
     * eapply tau_step; [reflexivity|]. destruct b; exact (IH _ _ _ H _ _ Plus).
     * inversion H; subst. eapply tau_step; [reflexivity|constructor].
   + inversion H; subst. eapply tau_trans; [exact (IH _ _ _ C _ _ Plus)|].
     eapply tau_step; [reflexivity|constructor].
 - (* addition as a call of the `+` primitive *)
   eapply tau_step; [cbn; rewrite push_free; reflexivity|].
   destruct (L.eval n env e1) as [[va|ea]|] eqn:A; try discriminate.
   + eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|]. cbn [tr_out].
     eapply tau_step; [reflexivity|].
     destruct (L.eval n env e2) as [[vb|eb]|] eqn:B; try discriminate.
     * eapply tau_trans; [exact (IH _ _ _ B _ _ Plus)|]. cbn [tr_out].
       destruct va, vb; inversion H; subst; (eapply tau_step; [cbn [next ctl kont mem ret_move rev app]; unfold call_named; match goal with |- context [lookup ?nm (gfuns s)] => replace (lookup nm (gfuns s)) with (Some (FPrim PAdd)) by (symmetry; exact Plus) end; reflexivity|constructor]).
     * inversion H; subst. eapply tau_trans; [exact (IH _ _ _ B _ _ Plus)|].
       eapply tau_step; [reflexivity|constructor].
   + inversion H; subst. eapply tau_trans; [exact (IH _ _ _ A _ _ Plus)|].
     eapply tau_step; [reflexivity|constructor].
Qed.

(* Corollary: closed Lambda.v programs that terminate give the same KLambda
   final outcome (value or error) in the empty continuation. *)
Corollary embed_final : forall e r s, L.evaluates [] e r ->
 lookup plus_name (gfuns s) = Some (FPrim PAdd) ->
 exists c, tau (Cfg (Eval [] (tr 0 e)) [] s) c /\
  final P c (match r with L.Returned v => Normal (tr_val v) | L.Raised x => Error (tr_err x) end).
Proof.
 intros e r s [n H] Plus. exists (Cfg (tr_out r) [] s); split.
 - exact (embed n [] e r H [] s Plus).
 - destruct r; reflexivity.
Qed.
End Sim.
End KLBridge.
