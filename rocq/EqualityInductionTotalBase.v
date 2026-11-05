(* BURI/EQ-1, obligation EQ1-TERM, part 1: the captured helper code of
   base.shen, equations.shen and spec/arithmetic.shen (and the runtime
   contracts) terminates under the actual Native evaluator on its domain,
   returning its reference value. One traced symbolic run per captured body
   (EqualityInductionTrace); recursion by structural induction on the
   decreasing argument (list tail, term structure, string length). *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native EqualityInductionOracle EqualityInductionModel EqualityInductionSpecs
 EqualityInductionHelpers EqualityInductionKernel EqualityInductionDrivers EqualityInductionRefinement
 EqualityInductionTrace.
Import ListNotations Native.Native.
Module EqualityInductionTotalBase.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionHelpers.EqualityInductionHelpers EqualityInductionKernel.EqualityInductionKernel
 EqualityInductionDrivers.EqualityInductionDrivers EqualityInductionRefinement.EqualityInductionRefinement
 EqualityInductionTrace.EqualityInductionTrace.
Open Scope string_scope.

Lemma ok_of : forall s vs w ps b, lookup program s = Some (Def ps b) -> agree defined dn b = true ->
 Nat.eqb (List.length ps) (List.length vs) = true -> Term oref (arguments ps vs) b ->
 (forall n v, run n program s vs = Returned v -> v = w) -> okcall (s,vs,w).
Proof.
 intros s vs w ps b L A Ar T P. destruct (total_def oref s ps b vs L A Ar T) as [n [v R]].
 exists n. rewrite <- (P _ _ R). exact R.
Qed.

Lemma pos_le1 : forall n, Z.leb 1 (Z.pos (Pos.of_succ_nat n)) = true.
Proof. intro n. apply Z.leb_le. lia. Qed.
Lemma ok_w : forall s vs w w', okcall (s,vs,w) -> w = w' -> okcall (s,vs,w').
Proof. intros s vs w w' H <-; exact H. Qed.

#[global] Arguments hide : simpl never.
#[local] Arguments String.eqb : simpl nomatch.
#[local] Arguments same : simpl nomatch.
#[local] Arguments Z.eqb : simpl nomatch.
#[local] Arguments Z.leb : simpl nomatch.
#[local] Arguments Z.geb : simpl nomatch.
#[local] Arguments Z.sub : simpl nomatch.

Ltac eqb_norm := repeat match goal with |- context [String.eqb ?s ?t] =>
 is_var s; tryif is_var t then fail else rewrite (String.eqb_sym s t) end.
Lemma prim_eq : forall s x, primitive "eq?" [Symbol s;x] = Some (Boolean (symeq s x)).
Proof. intros s x. destruct x; reflexivity. Qed.
Lemma symeq_true : forall s x, symeq s x = true -> x = Symbol s.
Proof. intros s x H. destruct x; try discriminate. cbn in H. apply String.eqb_eq in H. subst. reflexivity. Qed.
Ltac red_with X := cbn -[r_mem r_uniq r_app r_revh r_get r_keys r_remove r_allsym r_sig r_sort r_args r_ctx r_ctxh
 r_subst r_substs subst_var r_substitution r_rule r_fresh r_zip r_vars r_ihyps r_resolve r_head r_tail r_rapp
 r_inst r_replace r_rarg r_goal r_steps r_cases r_theorem r_bundle next1 bound1 csr1 after1 alldig unsigned ispell
 spelling sig_parts tagged theory_value rules_value signature_value constructors_value okcall symeq X].
(* eq? against a literal symbol is folded to [symeq] (a two-way test)
   instead of a case split over every shape of the tested value. *)
Ltac red_g := red_with primitive;
 repeat match goal with |- context [primitive "eq?" [Symbol ?s; ?x]] => rewrite (prim_eq s x) end;
 red_with okcall; try unfold sym; eqb_norm.
(* Split on the innermost stuck scrutinee of the goal; a boolean test of a
   variable learns the variable's shape only when the test succeeds. *)
Ltac tgen t := first [match goal with E : t = _ |- _ => rewrite E end
   | is_var t; destruct t
   | lazymatch type of t with bool => idtac end; lazymatch t with match ?y with _ => _ end => is_var y end;
     let E := fresh "T" in destruct t eqn:E; [lazymatch t with match ?y with _ => _ end => destruct y end; cbn in E; try discriminate E; try (match type of E with ?a = ?a => clear E end)|]
   | let E := fresh "E" in destruct t eqn:E].
Ltac tsplit t := lazymatch t with
 | match ?u with _ => _ end => first [is_var u; lazymatch type of t with bool => idtac end;
     let E := fresh "T" in destruct t eqn:E; [destruct u; cbn in E; try discriminate E; try (match type of E with ?a = ?a => clear E end)|]
   | tsplit u]
 | stepT ?o ?rho (hide ?x) => change (stepT o rho (hide x)) with (stepT o rho x)
 | String.get _ ?x => first [is_var x; destruct x | tgen t]
 | symeq ?s ?x => first [is_var x; let E := fresh "Q" in destruct (symeq s x) eqn:E; [apply symeq_true in E; subst x|] | tgen t]
 | String.eqb ?a ?x => first [is_var x; first [match goal with E : t = _ |- _ => rewrite E end | let E := fresh "S" in
   destruct (String.eqb a x) eqn:E; [apply String.eqb_eq in E; subst x|]] | tgen t]
 | _ => tgen t
 end.
Ltac tdrive := red_g; repeat (lazymatch goal with |- match ?t with _ => _ end => tsplit t end; red_g).
Ltac dnorm := repeat match goal with
 | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
 end.
Ltac dred H := cbn [idata numok lst kv wfr tm tms rl_ok zok sigok tmv var_of symv symeq single andb orb negb] in H.
Ltac dom := repeat match goal with H : @eq bool _ true |- _ => progress dred H end;
 repeat match goal with E : ?t = ?c, D : @eq bool ?u true |- _ => tryif is_var t then fail else
   (lazymatch c with true => idtac | false => idtac end; lazymatch u with context [t] => rewrite E in D; dred D end) end;
 dnorm.
Create HintDb tdb discriminated.
#[global] Hint Extern 3 (@eq bool _ true) => progress (cbn [idata numok lst kv wfr tm tms rl_ok zok sigok tmv var_of symv symeq single]); try (apply andb_true_intro; split) : tdb.
#[global] Hint Extern 2 (@eq bool (andb _ _) true) => apply andb_true_intro; split : tdb.
#[global] Hint Resolve kv_lst wfr_lst allsym_lst lst_keys ctx_kv ctxh_kv kv_app kv_remove zok_zip
 wfr_rules sigok_signature rl_resolve rl_rule substitution_kv wfr_ihyps : tdb.
Ltac contra0 := dom; first [discriminate | match goal with H : false = true |- _ => discriminate H
 | H : true = false |- _ => discriminate H
 | E : Z.leb _ _ = false |- _ => apply Z.leb_gt in E; lia
 | E : _ = false |- _ => rewrite ?pos_le1, ?Z.leb_refl in E; cbn in E; discriminate E end].
(* A failed test kept only its outcome; refute by learning the tested shape. *)
Ltac contraT := first [solve [contra0] | match goal with E : (match ?y with _ => _ end) = _ |- _ =>
 is_var y; destruct y; cbn in E; try discriminate E; contraT end].
Ltac weq := first [reflexivity | congruence | (unfold found, missing, mismatch, rejected, checked, sym in *; congruence)].
Ltac norm_leaf := idtac.
(* One symbolic run per body: structural recursion on a value through
   [vind], whose hypothesis is specialised at the leaves to the subterms the
   run has exposed. *)
Lemma vind : forall (P : value -> Prop), (forall v, (forall a b, v = Pair a b -> P a /\ P b) -> P v) -> forall v, P v.
Proof. intros P H v; induction v; apply H; intros a' b' E; inversion E; subst; auto. Qed.
Ltac vind_tac := lazymatch goal with |- forall v : value, @?G v => apply (vind G) end.
Ltac ihs := repeat match goal with IH : forall a b, Pair ?x ?y = Pair a b -> _ |- _ =>
   let H := fresh "IHs" in pose proof (IH x y eq_refl) as H; clear IH; cbv beta in H end;
 repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac okone := dom; first [solve [eapply ok_w; [solve [eauto 5 with tdb]|weq]]
 | match goal with E : (match ?y with _ => _ end) = _ |- _ => is_var y; destruct y; cbn in E; try discriminate E; okone end].
Ltac okleaf := norm_leaf; ihs; repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil end;
 try okone.
Ltac start b := unfold Term; let e := eval cbv [lazify map] in (lazify b) in change b with e.
Ltac tterm b := start b; tdrive; try contraT; okleaf.
Ltac tdef pc := lazymatch goal with |- okcall (?s,_,_) =>
 let d := eval vm_compute in (def_of s) in lazymatch d with Def ?ps ?b =>
 apply (ok_of s _ _ ps b); [vm_compute; reflexivity|vm_compute; reflexivity|reflexivity|tterm b|pc] end end.
Ltac pc_drv field := let n := fresh "n" in let v := fresh "v" in let R := fresh "R" in
 intros n v R; apply run_ask in R; exact (field _ (drivers (S n)) _ _ R).
Ltac pc_ask lemma := let n := fresh "n" in let v := fresh "v" in let R := fresh "R" in
 intros n v R; apply run_ask in R; eapply lemma; exact R.

(* Runtime contracts. *)
Lemma ok_eq : forall a b, okcall ("kl:=",[a;b],Boolean (same a b)).
Proof. intros a b. tdef ltac:(pc_ask ask_eq). Qed.
Lemma ok_assert : forall b, okcall ("kl:_scm.assert-boolean",[Boolean b],Boolean b).
Proof.
 intros b. tdef ltac:(idtac; let n := fresh "n" in let v := fresh "v" in let R := fresh "R" in
   intros n v R; apply run_ask in R; destruct (ask_assert _ _ _ R) as (b' & E1 & E2); rewrite E2; exact (eq_sym E1)).
Qed.
Lemma ok_symbol : forall w, okcall ("kl:symbol?",[w],Boolean (is_sym w)).
Proof. intros w. tdef ltac:(pc_ask ask_symbol). Qed.
Lemma ok_not : forall w, okcall ("kl:not",[w],Boolean (match w with Boolean false => true | _ => false end)).
Proof. intros w. tdef ltac:(pc_ask ask_not). Qed.
#[global] Hint Resolve ok_eq ok_assert ok_symbol ok_not : tdb.

(* base.shen *)
Lemma ok_member : forall ys x, lst ys = true -> okcall ("kl:buri.member?",[x;ys],Boolean (r_mem x ys)).
Proof. vind_tac; intros ys IH x D; tdef ltac:(pc_ask ask_member). Qed.
#[global] Hint Resolve ok_member : tdb.
Lemma ok_unique : forall xs, lst xs = true -> okcall ("kl:buri.unique?",[xs],Boolean (r_uniq xs)).
Proof. vind_tac; intros xs IH D; tdef ltac:(pc_ask ask_unique). Qed.
Lemma ok_append : forall xs ys, lst xs = true -> okcall ("kl:buri.append",[xs;ys],r_app xs ys).
Proof. vind_tac; intros xs IH ys D; tdef ltac:(pc_ask ask_append). Qed.
Lemma ok_revh : forall xs a, lst xs = true -> okcall ("kl:buri.rev-h",[xs;a],r_revh xs a).
Proof. vind_tac; intros xs IH a D; tdef ltac:(pc_ask ask_revh). Qed.
#[global] Hint Resolve ok_unique ok_append ok_revh : tdb.
Lemma ok_rev : forall xs, lst xs = true -> okcall ("kl:buri.rev",[xs],r_revh xs Nil).
Proof. intros xs D; tdef ltac:(pc_ask ask_rev). Qed.
Lemma ok_get : forall xs k, kv xs = true -> okcall ("kl:buri.get",[k;xs],r_get k xs).
Proof. vind_tac; intros xs IH k D; tdef ltac:(pc_ask ask_get). Qed.
Lemma ok_keys : forall xs, kv xs = true -> okcall ("kl:buri.keys",[xs],r_keys xs).
Proof. vind_tac; intros xs IH D; tdef ltac:(pc_ask ask_keys). Qed.
Lemma ok_remove : forall xs k, kv xs = true -> okcall ("kl:buri.remove",[k;xs],r_remove k xs).
Proof. vind_tac; intros xs IH k D; tdef ltac:(pc_ask ask_remove). Qed.
Lemma ok_allsym : forall xs, okcall ("kl:buri.all-symbols?",[xs],Boolean (r_allsym xs)).
Proof. vind_tac; intros xs IH; tdef ltac:(pc_ask ask_allsym). Qed.
#[global] Hint Resolve ok_rev ok_get ok_keys ok_remove ok_allsym : tdb.

(* Decimal spelling (EQ1-NUMERIC helpers); recursion on the string. *)
Ltac norm_leaf ::= rewrite ?Pos2Nat.inj_1; cbn [substring]; rewrite ?substring_all.
Lemma ok_digits : forall s, okcall ("kl:buri.digits?",[Text s],Boolean (alldig s)).
Proof. induction s as [|c s IH]; tdef ltac:(pc_drv d_digits). Qed.
#[global] Hint Resolve ok_digits : tdb.
Lemma ok_unsigned : forall s, okcall ("kl:buri.unsigned-spelling?",[Text s],Boolean (unsigned s)).
Proof. intros s. tdef ltac:(pc_drv d_unsigned). Qed.
#[global] Hint Resolve ok_unsigned : tdb.
Lemma ok_ispell : forall s, okcall ("kl:buri.integer-spelling?",[Text s],Boolean (ispell s)).
Proof. intros s. tdef ltac:(pc_drv d_ispell). Qed.
Lemma ok_str : forall z, okcall ("kl:str",[Integer z],Text (spelling z)).
Proof. intros z. tdef ltac:(pc_drv d_str). Qed.
#[global] Hint Resolve ok_ispell ok_str : tdb.
Lemma ok_exact : forall z, okcall ("kl:buri.exact-integer?",[Integer z],Boolean (ispell (spelling z))).
Proof. intros z. tdef ltac:(pc_drv d_exact). Qed.
#[global] Hint Resolve ok_exact : tdb.
Lemma ok_nat : forall i, numok i = true -> okcall ("kl:buri.nat?",[i],Boolean (match i with Integer z => Z.leb 0 z | _ => false end)).
Proof. intros i D. tdef ltac:(pc_drv d_nat). Qed.
#[global] Hint Resolve ok_nat : tdb.
Ltac norm_leaf ::= idtac.

(* Literal theory data: argument-free, so termination is a ground
   computation of the actual Native evaluator (vm-checked). *)
Lemma ok_signature : okcall ("kl:buri.signature",[],signature_value).
Proof. exists 1000. vm_compute. reflexivity. Qed.
Lemma ok_constructors : okcall ("kl:buri.constructors",[],constructors_value).
Proof. exists 1000. vm_compute. reflexivity. Qed.
Lemma ok_rules : okcall ("kl:buri.rules",[],rules_value).
Proof. exists 1000. vm_compute. reflexivity. Qed.
#[global] Hint Resolve ok_signature ok_constructors ok_rules : tdb.
Lemma ok_theory : okcall ("kl:buri.theory",[],theory_value).
Proof. exists 1000. vm_compute. reflexivity. Qed.
Lemma ok_sig : forall ss f, sigok ss = true -> okcall ("kl:buri.sig",[f;ss],r_sig f ss).
Proof. vind_tac; intros ss IH f D; tdef ltac:(pc_ask ask_sig). Qed.
#[global] Hint Resolve ok_theory ok_sig : tdb.

(* sort / sort-app / args?: structural on the term, args? before sort-app
   before sort at each term. *)
Definition S1 t := forall C, kv C = true -> okcall ("kl:buri.sort",[t;C],r_sort t C).
Definition S2 t := forall g C, kv C = true -> okcall ("kl:buri.sort-app",[g;t;C],
 match sig_parts g with Some (sorts,r) => if r_args t sorts C then found r else missing | None => missing end).
Definition S3 t := forall ss C, kv C = true -> okcall ("kl:buri.args?",[t;ss;C],Boolean (r_args t ss C)).
Lemma pc_sort : forall n t C v, run n program "kl:buri.sort" [t;C] = Returned v -> v = r_sort t C.
Proof. intros n t C v R. apply run_ask in R. exact (proj1 (ask_sorting _) _ _ _ R). Qed.
Lemma pc_sortapp : forall n g xs C v, run n program "kl:buri.sort-app" [g;xs;C] = Returned v -> v =
 match sig_parts g with Some (sorts,r) => if r_args xs sorts C then found r else missing | None => missing end.
Proof. intros n g xs C v R. apply run_ask in R. exact (proj1 (proj2 (ask_sorting _)) _ _ _ _ R). Qed.
Lemma pc_args : forall n xs ss C v, run n program "kl:buri.args?" [xs;ss;C] = Returned v -> v = Boolean (r_args xs ss C).
Proof. intros n xs ss C v R. apply run_ask in R. exact (proj2 (proj2 (ask_sorting _)) _ _ _ _ R). Qed.
Lemma s3_of : forall t, (forall a b, t = Pair a b -> S1 a /\ S3 b) -> S3 t.
Proof.
 intros t H ss C D. unfold S1, S3 in H. tdef ltac:(intros ? ? R; exact (pc_args _ _ _ _ _ R)).
Qed.
Lemma s2_of : forall t, S3 t -> S2 t.
Proof. intros t H3 g C D. unfold S3 in H3. tdef ltac:(intros ? ? R; exact (pc_sortapp _ _ _ _ _ R)). Qed.
Lemma s1_of : forall t, (forall a b, t = Pair a b -> S2 b) -> S1 t.
Proof.
 intros t H C D. unfold S2 in H. tdef ltac:(intros ? ? R; exact (pc_sort _ _ _ _ R)).
Qed.
Lemma ok_sorting : forall t, S1 t /\ S2 t /\ S3 t.
Proof.
 induction t as [| | | | | | |a [A1 [A2 A3]] b [B1 [B2 B3]]| |];
 (match goal with |- S1 ?t /\ _ => assert (T3 : S3 t) by (apply s3_of; intros a' b' E; inversion E; subst; split; assumption) end;
  split; [|split; [apply s2_of; exact T3|exact T3]];
  apply s1_of; intros a' b' E; inversion E; subst; assumption).
Qed.
Lemma ok_sort : forall t C, kv C = true -> okcall ("kl:buri.sort",[t;C],r_sort t C).
Proof. intro t. exact (proj1 (ok_sorting t)). Qed.
#[global] Hint Resolve ok_sort : tdb.

(* contexts *)
Lemma ok_ctxh : forall C, okcall ("kl:buri.context-h?",[C],Boolean (r_ctxh C)).
Proof. vind_tac; intros C IH; tdef ltac:(pc_ask ask_ctxh). Qed.
#[global] Hint Resolve ok_ctxh : tdb.
Lemma ok_ctx : forall C, okcall ("kl:buri.context?",[C],Boolean (r_ctx C)).
Proof. intro C. tdef ltac:(pc_ask ask_ctx). Qed.
#[global] Hint Resolve ok_ctx : tdb.

End EqualityInductionTotalBase.
