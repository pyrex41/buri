(* BURI/EQ-1, obligation EQ1-TERM, part 2: termination of the captured
   substitution, rule lookup and kernel.shen leaf helpers on their domains
   (same technique as EqualityInductionTotalBase). *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native EqualityInductionOracle EqualityInductionModel EqualityInductionSpecs
 EqualityInductionHelpers EqualityInductionKernel EqualityInductionDrivers EqualityInductionRefinement
 EqualityInductionTrace EqualityInductionTotalBase.
Import ListNotations Native.Native.
Module EqualityInductionTotalTerms.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionHelpers.EqualityInductionHelpers EqualityInductionKernel.EqualityInductionKernel
 EqualityInductionDrivers.EqualityInductionDrivers EqualityInductionRefinement.EqualityInductionRefinement
 EqualityInductionTrace.EqualityInductionTrace EqualityInductionTotalBase.EqualityInductionTotalBase.
Open Scope string_scope.
#[local] Arguments String.eqb : simpl nomatch.
#[local] Arguments same : simpl nomatch.
#[local] Arguments Z.eqb : simpl nomatch.
#[local] Arguments Z.leb : simpl nomatch.
#[local] Arguments Z.geb : simpl nomatch.
#[local] Arguments Z.sub : simpl nomatch.

(* substitution *)
Lemma get_shape : forall k xs, r_get k xs = missing \/ exists v, r_get k xs = found v.
Proof.
 intro k; induction xs as [| | | | | | |a _ b IH| |]; try (left; reflexivity).
 destruct a as [| | | | | | |j [| | | | | | |v [| | | | | | | | |]| |]| |]; try (left; reflexivity).
 cbn [r_get]. destruct (same k j); [right; exists v; reflexivity|exact IH].
Qed.
Lemma ok_substvar : forall x k xs, okcall ("kl:buri.subst-var",[x;r_get k xs],subst_var x (r_get k xs)).
Proof.
 intros x k xs. destruct (get_shape k xs) as [E|[v E]]; rewrite E; tdef ltac:(pc_ask ask_substvar).
Qed.
#[global] Hint Resolve ok_substvar : tdb.
Lemma pc_subst : forall n t sub v, run n program "kl:buri.subst" [t;sub] = Returned v -> v = r_subst t sub.
Proof. intros n t sub v R. apply run_ask in R. exact (proj1 (ask_substitute _) _ _ _ R). Qed.
Lemma pc_substs : forall n a sub v, run n program "kl:buri.substs" [a;sub] = Returned v -> v = r_substs a sub.
Proof. intros n a sub v R. apply run_ask in R. exact (proj2 (ask_substitute _) _ _ _ R). Qed.
Lemma ok_substitute : forall t,
 (forall sub, tm t = true -> kv sub = true -> okcall ("kl:buri.subst",[t;sub],r_subst t sub)) /\
 (forall sub, tms t = true -> kv sub = true -> okcall ("kl:buri.substs",[t;sub],r_substs t sub)).
Proof.
 vind_tac; intros t IH; split; intros sub D K;
 [tdef ltac:(intros ? ? R; exact (pc_subst _ _ _ _ R)) | tdef ltac:(intros ? ? R; exact (pc_substs _ _ _ _ R))].
Qed.
Lemma ok_subst : forall t sub, tm t = true -> kv sub = true -> okcall ("kl:buri.subst",[t;sub],r_subst t sub).
Proof. intro t. exact (proj1 (ok_substitute t)). Qed.
#[global] Hint Resolve ok_subst : tdb.
Lemma ok_substitution : forall vars sub C, kv C = true ->
 okcall ("kl:buri.substitution?",[vars;sub;C],Boolean (r_substitution vars sub C)).
Proof.
 vind_tac; intros vars IH sub C D; tdef ltac:(idtac; let n := fresh in let v := fresh in let R := fresh in
   intros n v R; exact (native_substitution _ _ _ _ _ R)).
Qed.
#[global] Hint Resolve ok_substitution : tdb.
Lemma ok_rule : forall rs n, wfr rs = true -> okcall ("kl:buri.rule",[n;rs],r_rule n rs).
Proof. vind_tac; intros rs IH nm D; tdef ltac:(pc_ask ask_rule). Qed.
#[global] Hint Resolve ok_rule : tdb.

(* kernel.shen leaf helpers *)
Lemma ok_fresh : forall xs ys, lst xs = true -> lst ys = true -> okcall ("kl:buri.fresh?",[xs;ys],Boolean (r_fresh xs ys)).
Proof. vind_tac; intros xs IH ys D1 D2; tdef ltac:(pc_ask ask_fresh). Qed.
Lemma ok_ziph : forall x y z, okcall ("kl:buri.zip-h",[x;y;z],
 match tagged "zipped" z with Some zs => L [sym "zipped";Pair (L [x;y]) zs] | None => mismatch end).
Proof. intros x y z. tdef ltac:(pc_ask ask_ziph). Qed.
#[global] Hint Resolve ok_fresh ok_ziph : tdb.
Lemma ok_zip : forall xs ys, okcall ("kl:buri.zip",[xs;ys],r_zip xs ys).
Proof. vind_tac; intros xs IH ys; tdef ltac:(pc_ask ask_zip). Qed.
Lemma ok_vars : forall ns, lst ns = true -> okcall ("kl:buri.variables",[ns],r_vars ns).
Proof. vind_tac; intros ns IH D; tdef ltac:(pc_ask ask_vars). Qed.
Lemma ok_ihyps : forall bs x g l r, lst bs = true -> tm l = true -> tm r = true ->
 okcall ("kl:buri.induction-hyps",[bs;x;g;l;r],r_ihyps bs x g l r).
Proof. vind_tac; intros bs IH x g l r D Dl Dr; tdef ltac:(pc_ask ask_ihyps). Qed.
#[global] Hint Resolve ok_zip ok_vars ok_ihyps : tdb.
Lemma ok_resolve : forall ref hs ls, wfr hs = true -> wfr ls = true -> okcall ("kl:buri.resolve",[ref;hs;ls],r_resolve ref hs ls).
Proof. intros ref hs ls D1 D2. tdef ltac:(pc_ask ask_resolve). Qed.
Lemma ok_head : forall x ts, okcall ("kl:buri.replace-head",[x;ts],r_head x ts).
Proof. intros x ts. tdef ltac:(pc_ask ask_head). Qed.
Lemma ok_tail : forall t x, okcall ("kl:buri.replace-tail",[t;x],r_tail t x).
Proof. intros t x. tdef ltac:(pc_ask ask_tail). Qed.
Lemma ok_rapp : forall f x, okcall ("kl:buri.replace-app",[f;x],r_rapp f x).
Proof. intros f x. tdef ltac:(pc_ask ask_rapp). Qed.
#[global] Hint Resolve ok_resolve ok_head ok_tail ok_rapp : tdb.
Lemma ok_inst : forall rl sub C, rl_ok rl = true -> kv C = true -> okcall ("kl:buri.instantiate",[rl;sub;C],r_inst rl sub C).
Proof. intros rl sub C D1 D2. tdef ltac:(intros ? ? R; exact (native_instantiate _ _ _ _ _ R)). Qed.
Lemma ok_goal : forall C l r, okcall ("kl:buri.goal?",[C;l;r],Boolean (r_goal C l r)).
Proof. intros C l r. tdef ltac:(intros ? ? R; exact (native_goal _ _ _ _ _ R)). Qed.
#[global] Hint Resolve ok_inst ok_goal : tdb.

(* replace / replace-arg: structural on the path, then on the argument list. *)
Definition Rp p := forall t a b, idata p = true -> okcall ("kl:buri.replace",[t;p;a;b],r_replace t p a b).
Definition Ra is := forall args z a b, idata is = true -> okcall ("kl:buri.replace-arg",[args;Integer z;is;a;b],r_rarg args z is a b).
Lemma pc_rarg : forall n args z is a b v, run n program "kl:buri.replace-arg" [args;Integer z;is;a;b] = Returned v ->
 v = r_rarg args z is a b.
Proof. intros n args z is a b v R. apply run_ask in R. exact (d_rarg _ (drivers (S n)) _ _ _ _ _ _ R). Qed.
Lemma ra_of : forall is, Rp is -> Ra is.
Proof.
 intros is P. unfold Rp in P. unfold Ra. vind_tac; intros args IH zz a0 b0 D;
 tdef ltac:(intros ? ? R; exact (pc_rarg _ _ _ _ _ _ _ R)).
Qed.
Lemma rarg_of_rp : forall is args z a b, Rp is -> idata is = true ->
 okcall ("kl:buri.replace-arg",[args;Integer z;is;a;b],r_rarg args z is a b).
Proof. intros is args z a b P D. exact (ra_of is P args z a b D). Qed.
#[local] Hint Resolve rarg_of_rp : tdb.
Lemma ok_replacing : forall p, Rp p.
Proof.
 vind_tac; intros p IH; unfold Rp; intros t0 a0 b0 D;
 tdef ltac:(intros ? ? R; exact (native_replace _ _ _ _ _ _ R)).
Qed.
Lemma ok_replace : forall t p a b, idata p = true -> okcall ("kl:buri.replace",[t;p;a;b],r_replace t p a b).
Proof. intros t p. exact (ok_replacing p t). Qed.
Lemma ok_rarg : forall args z is a b, idata is = true -> okcall ("kl:buri.replace-arg",[args;Integer z;is;a;b],r_rarg args z is a b).
Proof. intros args z is. exact (ra_of is (ok_replacing is) args z). Qed.
#[global] Hint Resolve ok_replace ok_rarg : tdb.
End EqualityInductionTotalTerms.
