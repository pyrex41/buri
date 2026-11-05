(* Captured EQ-1 code, part 2: the remaining equations.shen helpers and the
   leaf helpers of shen/kernel.shen compute their EqualityInductionModel
   reference functions (partial correctness: every value the Native evaluator
   returns is the reference value). Not covered here, and listed as open
   obligations in docs/EQ1.md: buri.substitution?, buri.instantiate,
   buri.replace/replace-arg, and the recursive kernel drivers
   (check-steps, check-step-result, after-rewrite, check-cases,
   check-case-bound, check-theorem, bundle-h, bundle-next, check-bundle). *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeHelpers EqualityInductionOracle EqualityInductionModel EqualityInductionSpecs
 EqualityInductionKernelInput.
Import ListNotations Native.Native.
Module EqualityInductionHelpers.
Module O := EqualityInductionOracle.EqualityInductionOracle.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs.
Open Scope string_scope.

Ltac learn E ::= lazymatch type of E with
 | (match ?y with _ => _ end) = ?c => vvar y; positive c; destruct y; tidy;
   try (lazymatch type of E with ?a = ?b => is_var b; subst b end)
 end.
Ltac split_term t ::= lazymatch t with
 | match ?y with _ => _ end => first [is_var y; lazymatch type of t with expr => fail | value => fail | _ => idtac end;
     let E := fresh "E" in destruct t eqn:E; try learn E
   | vvar y; destruct y
   | split_term y]
 | same ?a ?b => decide_bool (same a b)
 | String.eqb ?a ?b => decide_bool (String.eqb a b)
 | _ => lazymatch type of t with
   | bool => let E := fresh "E" in destruct t eqn:E
   | option _ => let E := fresh "E" in destruct t eqn:E end
 end.
(* For the kernel, injections must not normalise name comparisons. *)
Ltac tidy ::= repeat match goal with
 | E : (match _ with _ => _ end) = _ |- _ => progress cbn beta iota in E
 | E : ?a = ?b |- _ => constr_eq a b; clear E
 | E : _ = _ |- _ => discriminate E
 | E : Some _ = Some _ |- _ => apply some_inj in E
 | E : Boolean _ = Boolean _ |- _ => apply bool_inj in E
 end.
Ltac finish H ::= lazymatch type of H with
 | Some _ = Some _ => apply some_inj in H; finish H
 | None = Some _ => discriminate H
 | ?a = ?b => first [is_var b; subst b | is_var a; subst a | discriminate H | idtac]
 end.
Ltac norm_tests := repeat match goal with
 | E : _ = true |- _ => progress cbn [r_mem r_uniq r_keys r_allsym r_fresh L fold_right orb andb negb is_sym] in E
 | E : _ = false |- _ => progress cbn [r_mem r_uniq r_keys r_allsym r_fresh L fold_right orb andb negb is_sym] in E
 end.
Ltac close ::= leaf; tidy; unfold sym in *; repeat match goal with E : ?a = ?b |- _ => is_var b; subst b end;
 unfold r_ctx, r_goal, r_resolve, r_inst, r_head, r_tail, r_rapp, subst_var, is_missing, one;
 cbn -[same String.eqb ask signature_value rules_value theory_value constructors_value r_sort r_args];
 norm_tests; unfold sym in *; rewrite_known; refold.
Ltac solve_leaf ::= close; cbn -[same String.eqb ask signature_value rules_value theory_value constructors_value r_sort r_args]; try reflexivity;
 try (repeat (match goal with |- context [match ?y with _ => _ end] => vvar y; destruct y end);
   cbn -[signature_value rules_value theory_value constructors_value r_sort r_args]; rewrite_known; reflexivity).
Lemma ask_ctxh : forall k C v, ask k "kl:buri.context-h?" [C] = Some v -> v = Boolean (r_ctxh C).
Proof. induction k as [|k IH]; intros C v; [discriminate|]. spec_proof ltac:(fun H => first [known3 H | apply IH in H; finish H]). Qed.
Lemma ask_ctx : forall k C v, ask k "kl:buri.context?" [C] = Some v -> v = Boolean (r_ctx C).
Proof.
 intros [|k] C v; [discriminate|].
 spec_proof ltac:(fun H => first [known3 H | apply ask_ctxh in H; finish H]).
Qed.
Lemma ask_substvar : forall k x b v, ask k "kl:buri.subst-var" [x;b] = Some v -> v = subst_var x b.
Proof. intros [|k] x b v; [discriminate|]. spec_proof ltac:(fun H => first [known3 H | idtac]). Qed.
Lemma ask_substitute : forall k,
 (forall t sub v, ask k "kl:buri.subst" [t;sub] = Some v -> v = r_subst t sub) /\
 (forall a sub v, ask k "kl:buri.substs" [a;sub] = Some v -> v = r_substs a sub).
Proof.
 induction k as [|k (IHt & IHa)]; [split; intros; discriminate|]. split.
 - intros t sub v. spec_proof ltac:(fun H => first [known3 H | apply ask_substvar in H; finish H
     | apply IHt in H; finish H | apply IHa in H; finish H]).
 - intros a sub v. spec_proof ltac:(fun H => first [known3 H | apply IHt in H; finish H | apply IHa in H; finish H]).
Qed.
Lemma ask_subst : forall k t sub v, ask k "kl:buri.subst" [t;sub] = Some v -> v = r_subst t sub.
Proof. intro k; exact (proj1 (ask_substitute k)). Qed.
Ltac known4 H := first [known3 H | lazymatch type of H with
 | ask _ "kl:buri.sort" _ = _ => apply ask_sort in H; finish H
 | ask _ "kl:buri.context?" _ = _ => apply ask_ctx in H; finish H
 | ask _ "kl:buri.subst" _ = _ => apply ask_subst in H; finish H
 end].
Lemma ask_rule : forall k n rs v, ask k "kl:buri.rule" [n;rs] = Some v -> v = r_rule n rs.
Proof. induction k as [|k IH]; intros n rs v; [discriminate|]. spec_proof ltac:(fun H => first [known4 H | apply IH in H; finish H]). Qed.
Ltac known5 H := first [known4 H | lazymatch type of H with
 | ask _ "kl:buri.rule" _ = _ => apply ask_rule in H; finish H
 end].
(* kernel.shen helpers. *)
Lemma ask_fresh : forall k xs ys v, ask k "kl:buri.fresh?" [xs;ys] = Some v -> v = Boolean (r_fresh xs ys).
Proof. induction k as [|k IH]; intros xs ys v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | apply IH in H; finish H]). Qed.
Lemma ask_ziph : forall k x y z v, ask k "kl:buri.zip-h" [x;y;z] = Some v ->
 v = match tagged "zipped" z with Some zs => L [sym "zipped";Pair (L [x;y]) zs] | None => mismatch end.
Proof. intros [|k] x y z v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | idtac]). Qed.
Lemma ask_zip : forall k xs ys v, ask k "kl:buri.zip" [xs;ys] = Some v -> v = r_zip xs ys.
Proof. induction k as [|k IH]; intros xs ys v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | apply ask_ziph in H; finish H | apply IH in H; finish H]). Qed.
Lemma ask_vars : forall k ns v, ask k "kl:buri.variables" [ns] = Some v -> v = r_vars ns.
Proof. induction k as [|k IH]; intros ns v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | apply IH in H; finish H]). Qed.
Lemma ask_ihyps : forall k bs x g l r v, ask k "kl:buri.induction-hyps" [bs;x;g;l;r] = Some v -> v = r_ihyps bs x g l r.
Proof. induction k as [|k IH]; intros bs x g l r v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | apply IH in H; finish H]). Qed.
Lemma ask_resolve : forall k ref hs ls v, ask k "kl:buri.resolve" [ref;hs;ls] = Some v -> v = r_resolve ref hs ls.
Proof. intros [|k] ref hs ls v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | idtac]). Qed.
Lemma ask_head : forall k x ts v, ask k "kl:buri.replace-head" [x;ts] = Some v -> v = r_head x ts.
Proof. intros [|k] x ts v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | idtac]). Qed.
Lemma ask_tail : forall k t x v, ask k "kl:buri.replace-tail" [t;x] = Some v -> v = r_tail t x.
Proof. intros [|k] t x v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | idtac]). Qed.
Lemma ask_rapp : forall k f x v, ask k "kl:buri.replace-app" [f;x] = Some v -> v = r_rapp f x.
Proof. intros [|k] f x v; [discriminate|]. spec_proof ltac:(fun H => first [known5 H | idtac]). Qed.
Ltac known6 H := first [known5 H | lazymatch type of H with
 | ask _ "kl:buri.fresh?" _ = _ => apply ask_fresh in H; finish H
 | ask _ "kl:buri.zip" _ = _ => apply ask_zip in H; finish H
 | ask _ "kl:buri.variables" _ = _ => apply ask_vars in H; finish H
 | ask _ "kl:buri.induction-hyps" _ = _ => apply ask_ihyps in H; finish H
 | ask _ "kl:buri.resolve" _ = _ => apply ask_resolve in H; finish H
 | ask _ "kl:buri.replace-head" _ = _ => apply ask_head in H; finish H
 | ask _ "kl:buri.replace-tail" _ = _ => apply ask_tail in H; finish H
 | ask _ "kl:buri.replace-app" _ = _ => apply ask_rapp in H; finish H
 | ask _ "kl:buri.nat?" _ = _ => let E := fresh "N" in let z := fresh "z" in let Z := fresh "Z" in
     apply ask_nat in H; destruct H as [H|[H (z & E & Z)]]; finish H; try finish E
 end].
Lemma head_pos : forall w xs ts, r_head w xs = L [sym "replaced-args";ts] ->
 exists t, w = L [sym "replaced";t] /\ ts = Pair t xs.
Proof.
 intros w xs ts H. unfold r_head in H. destruct (tagged "replaced" w) eqn:T; [|discriminate].
 apply tagged_shape in T. cbn in H. injection H as <-. eauto.
Qed.
Lemma tail_pos : forall x w ts, r_tail x w = L [sym "replaced-args";ts] ->
 exists ts', w = L [sym "replaced-args";ts'] /\ ts = Pair x ts'.
Proof.
 intros x w ts H. unfold r_tail in H. destruct (tagged "replaced-args" w) eqn:T; [|discriminate].
 apply tagged_shape in T. cbn in H. injection H as <-. eauto.
Qed.
Lemma rapp_pos : forall f w t, r_rapp f w = L [sym "replaced";t] ->
 exists ts, w = L [sym "replaced-args";ts] /\ t = Pair f ts.
Proof.
 intros f w t H. unfold r_rapp in H. destruct (tagged "replaced-args" w) eqn:T; [|discriminate].
 apply tagged_shape in T. cbn in H. injection H as <-. eauto.
Qed.
(* From the actual Native evaluator to the oracle semantics. *)
Theorem run_ask : forall n s vs v, run n program s vs = Returned v -> ask (S n) s vs = Some v.
Proof.
 intros n s vs v H. unfold run in H. destruct (lookup program s) as [d|] eqn:D; [|discriminate].
 destruct (Nat.eqb _ _) eqn:Q; [|discriminate].
 rewrite (ask_unfold n s vs d D), Q. exact (O.eval_oracle program defined defined_lookup _ _ _ _ H).
Qed.
Theorem native_sort : forall n t C v, run n program "kl:buri.sort" [t;C] = Returned v -> v = r_sort t C.
Proof. intros; eapply ask_sort; apply run_ask; eassumption. Qed.
Theorem native_subst : forall n t sub v, run n program "kl:buri.subst" [t;sub] = Returned v -> v = r_subst t sub.
Proof. intros; eapply ask_subst; apply run_ask; eassumption. Qed.
Theorem native_context : forall n C v, run n program "kl:buri.context?" [C] = Returned v -> v = Boolean (r_ctx C).
Proof. intros; eapply ask_ctx; apply run_ask; eassumption. Qed.
Theorem native_rule : forall n name rs v, run n program "kl:buri.rule" [name;rs] = Returned v -> v = r_rule name rs.
Proof. intros; eapply ask_rule; apply run_ask; eassumption. Qed.
Theorem native_theory : forall n v, run n program "kl:buri.theory" [] = Returned v -> v = theory_value.
Proof. intros; eapply ask_theory; apply run_ask; eassumption. Qed.
Theorem native_ihyps : forall n bs x g l r v, run n program "kl:buri.induction-hyps" [bs;x;g;l;r] = Returned v ->
 v = r_ihyps bs x g l r.
Proof. intros; eapply ask_ihyps; apply run_ask; eassumption. Qed.
Theorem native_zip : forall n xs ys v, run n program "kl:buri.zip" [xs;ys] = Returned v -> v = r_zip xs ys.
Proof. intros; eapply ask_zip; apply run_ask; eassumption. Qed.
End EqualityInductionHelpers.
