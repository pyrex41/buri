(* E2E-15: composition of the proved Shen-Scheme passes on the captured code,
   and the honest semantic relation of the conditional and equality branches.

   1. compile-expression's let clause is (merge-nested-lets (emit-let ...))
      (pinned src/compiler.shen, checked literally by check-upstream-pass.py).
      When the body is a static application, its compilation is the captured
      order-call. `order_then_merge_preserves` composes the captured ordering
      pass with the captured merge on its actual output; `let_clause_preserves`
      composes captured emit-let, ordering and merge.
   2. Conditionals keep the boolean condition domain (`strict_if`); a cond
      whose emitted clauses have no literal #t test is outside the reader
      (`cond_without_true_unread`): the profile's XCondFail is NOT what the
      native port does (it returns #<void>), recorded as a refuted obligation.
   3. Equality: the eqv? lowering is related to KLambda = only for exact
      integers; mixed exactness is outside the numeric model and the native
      disagreement is recorded as a refuted obligation. *)
From Coq Require Import List String ZArith Bool Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep DecodeFacts
  OrderCallCorrect OrderCallPass OrderCallPreserve SchemeBranches.
Import ListNotations.
Module SchemeCompose.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module D := DecodeFacts.DecodeFacts.
Module Pass := OrderCallPass.OrderCallPass.
Module Pre := OrderCallPreserve.OrderCallPreserve.
Module B := SchemeBranches.SchemeBranches.
Open Scope string_scope.

(* ---------- 1. ordering composed with let merging ---------- *)
(* The let form exactly as emit-let builds it, before merging. *)
Definition naive_let x cv c := L [Symbol "let"; L [L [Symbol x; cv]]; c].

Lemma keyword_neq : forall f, ~ In f D.keywords -> String.eqb "let*" f = false /\ String.eqb "let" f = false.
Proof. intros f K. split; apply String.eqb_neq; intro E; apply K; subst; cbn; tauto. Qed.
Lemma bound_bind : forall rho x v es, Pre.bound_args rho es -> Pre.bound_args (Native.bind rho x v) es.
Proof. intros rho x v es Bd s I. unfold Native.bind. destruct (String.eqb s x); [discriminate|]. exact (Bd s I). Qed.

Lemma order_target : forall gen N f args es st0 c st0' tr0,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st0 (Out (Returned c) st0' tr0) ->
 Pass.shaped f c /\ exists T, Pre.DOrd f [] es T /\ decode (S (S N)) c = Some T /\ Pre.target_shape f N c T.
Proof.
 intros gen N f args es st0 c st0' tr0 K Dc NL H.
 destruct (keyword_neq f K) as [Q1 Q2].
 destruct (Pass.order_call_success gen f args st0 c st0' tr0 Q1 Q2 H) as [Ord Sh].
 split; [exact Sh|].
 rewrite D.decode_call in Dc by exact K.
 destruct (D.dmany (decode N) args) as [es'|] eqn:A; [|discriminate Dc]. inversion Dc; subst es'. clear Dc.
 inversion Ord as [|x xs r u o Kp Ord'|x xs r u name o Kp Occ Ord']; subst.
 - exact (Pre.ord_decode f N K args [Symbol f] (L (Symbol f :: args)) c Ord' [] [] es eq_refl eq_refl A
     (Pre.covers_args f args) (or_introl (Forall_nil _)) NL).
 - unfold Pass.keep in Kp. cbn in Kp. discriminate Kp.
Qed.

(* For every generator and every successful run of the captured ordering pass
   on an admitted call, the captured merge-nested-lets applied to the let that
   emit-let builds around that output returns syntax read as a target with
   exactly the completed outcomes (value, error, unsupported), final state and
   trace of the unordered, unmerged let, for every program, operation set,
   environment binding the call's variable arguments, and state. *)
Theorem order_then_merge_preserves : forall cexp ordc ext ys1 ys2 gen N f args es x cv a st0 c st0' tr0,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 decode (S N) cv = Some a ->
 evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st0 (Out (Returned c) st0' tr0) ->
 exists merged target,
  B.returns cexp ordc ext ys1 ys2 "kl:_scm.merge-nested-lets" [naive_let x cv c] merged /\
  decode (S (S (S N))) (naive_let x cv (L (Symbol f :: args))) = Some (Let x a (Call f es)) /\
  decode (S (S N)) merged = Some target /\
  forall p op rho st out, Pre.bound_args rho es ->
   (ev p op rho (Let x a (Call f es)) st out <-> ev p op rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 gen N f args es x cv a st0 c st0' tr0 K Dc NL Dv H.
 destruct (keyword_neq f K) as [Q1 Q2].
 destruct (order_target gen N f args es st0 c st0' tr0 K Dc NL H) as [Sh [T [DT [DCT TS]]]].
 destruct (Pre.merge_decode f N x cv a c T Q1 Q2 Dv DCT TS) as [DM _].
 exists (Pass.merge_spec (L [Symbol x; cv]) c), (Let x a T). split; [|split; [|split]].
 - exact (B.merge_shaped cexp ordc ext ys1 ys2 f (L [Symbol x; cv]) c Q1 Q2 Sh).
 - unfold naive_let. rewrite Pre.decode_let1, (D.decode_succ _ _ _ Dc), (D.decode_succ _ _ _ Dv). reflexivity.
 - exact DM.
 - intros p op rho st out Bd. apply ev_let_congr. intros v s o.
   exact (Pre.dord_preserves p op f [] es T DT (Native.bind rho x v) s o (bound_bind rho x v es Bd)).
Qed.

Lemma emit_let_success : forall cexp ordc ext ys1 ys2 x v b s st m st1 tr1,
 evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.emit-let" [x; v; b; s] st (Out (Returned m) st1 tr1) ->
 exists cv s1 e1 cb e2, cexp v s st = Out (Returned cv) s1 e1 /\ cexp b (Pair x s) s1 = Out (Returned cb) st1 e2 /\
  tr1 = (e1 ++ e2)%list /\ m = L [Symbol "let"; L [L [x; cv]]; cb].
Proof.
 intros cexp ordc ext ys1 ys2 x v b s st m st1 tr1 H.
 apply (B.emit_let_exact cexp ordc ext ys1 ys2 x v b s st) in H. destruct H as [_ E].
 unfold B.emit_let_spec, bind, ret, return_result in E.
 destruct (cexp v s st) as [[cv| | |] s1 e1] eqn:X1; cbn in E; try discriminate E.
 destruct (cexp b (Pair x s) s1) as [[cb| | |] s2 e2] eqn:X2; cbn in E; try discriminate E.
 inversion E; subst. exists cv, s1, e1, cb, e2. rewrite app_nil_r. auto.
Qed.

(* The whole let clause as compile-expression invokes it: captured emit-let,
   then captured merge-nested-lets on its result. The two compile-expression
   calls emit-let makes are uncaptured; the premises say what they return:
   the bound value is read as `a`, and the body, a static application, is
   compiled by the captured order-call (its emit-static-application route). *)
Theorem let_clause_preserves : forall cexp ordc ext ys1 ys2 gen N f args es x v b s a st m st1 tr1 r st2 tr2,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 (forall st' cv st'' tr, cexp v s st' = Out (Returned cv) st'' tr -> decode (S N) cv = Some a) ->
 (forall st' cb st'' tr, cexp b (Pair (Symbol x) s) st' = Out (Returned cb) st'' tr ->
   exists st0 st0' tr0, evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L (Symbol f :: args)] st0 (Out (Returned cb) st0' tr0)) ->
 evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.emit-let" [Symbol x; v; b; s] st (Out (Returned m) st1 tr1) ->
 evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.merge-nested-lets" [m] st1 (Out (Returned r) st2 tr2) ->
 exists target, decode (S (S N)) r = Some target /\ st2 = st1 /\ tr2 = [] /\
  forall p op rho st out, Pre.bound_args rho es ->
   (ev p op rho (Let x a (Call f es)) st out <-> ev p op rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 gen N f args es x v b s a st m st1 tr1 r st2 tr2 K Dc NL CV CB EL MG.
 destruct (emit_let_success cexp ordc ext ys1 ys2 _ v b s st m st1 tr1 EL) as [cv [s1 [e1 [cb [e2 [E1 [E2 [_ M]]]]]]]].
 subst m. pose proof (CV _ _ _ _ E1) as Dv. destruct (CB _ _ _ _ E2) as [st0 [st0' [tr0 O]]].
 destruct (order_then_merge_preserves cexp ordc ext ys1 ys2 gen N f args es x cv a st0 cb st0' tr0 K Dc NL Dv O)
  as [merged [target [R [_ [DT EQ]]]]].
 pose proof (evapp_det _ _ _ _ _ _ _ MG (R st1)) as X. inversion X; subst.
 exists target. auto.
Qed.

(* ---------- 2. conditionals ---------- *)
Definition assert_contract (op : string -> list value -> computation) :=
 (forall b st, op "kl:_scm.assert-boolean" [Boolean b] st = Out (Returned (Boolean b)) st []) /\
 (forall v st, (forall b, v <> Boolean b) -> stops (op "kl:_scm.assert-boolean" [v] st)).
(* The primitive contract the compiler's own world uses satisfies it. *)
Lemma world_assert_contract : forall cexp ordc ext ys1 ys2, assert_contract (B.op cexp ordc ext ys1 ys2).
Proof.
 intros. split; [intros b st; reflexivity|].
 intros v st N w E. destruct v as [| | | | | |b| | |]; try (cbv in E; discriminate E). exact (N b eq_refl).
Qed.

(* A forced condition keeps the KLambda condition domain: true selects the
   then-branch, false the else-branch, anything else never selects a branch
   (the assert-boolean outcome is the result), and only the selected branch's
   effects occur. Universal over programs, operations, environments, states. *)
Theorem strict_if : forall p op rho c a b st out, p "kl:_scm.assert-boolean" = None -> assert_contract op ->
 (ev p op rho (If (Call "kl:_scm.assert-boolean" [c]) a b) st out <->
  (exists bv s1 e1 o2, ev p op rho c st (Out (Returned (Boolean bv)) s1 e1) /\
     ev p op rho (if bv then a else b) s1 o2 /\ out = after e1 o2) \/
  (exists v s1 e1, (forall bb, v <> Boolean bb) /\ ev p op rho c st (Out (Returned v) s1 e1) /\
     completed out /\ out = after e1 (op "kl:_scm.assert-boolean" [v] s1)) \/
  (ev p op rho c st out /\ stops out)).
Proof.
 intros p op rho c a b st out Pf [AT AF].
 assert (CALL : forall o, ev p op rho (Call "kl:_scm.assert-boolean" [c]) st o <->
   (exists v s1 e1, ev p op rho c st (Out (Returned v) s1 e1) /\ completed o /\
      o = after e1 (op "kl:_scm.assert-boolean" [v] s1)) \/ (ev p op rho c st o /\ stops o)).
 { intro o. rewrite ev_call. rewrite (evs_cons p op rho c [] _ st o (fun vs => apply_monotone _ _ _ _)).
   split.
   - intros [[v [s1 [e1 [o2 [A [B E]]]]]]|R]; [left|right; exact R].
     rewrite evs_nil in B.
     change (conv (fun n => apply n p op "kl:_scm.assert-boolean" [v]) s1 o2) with (evapp p op "kl:_scm.assert-boolean" [v] s1 o2) in B.
     rewrite (evapp_op p op _ _ s1 o2 Pf) in B. destruct B as [C B]. exists v, s1, e1. subst.
     split; [exact A|]. split; [apply B.completed_after; exact C|reflexivity].
   - intros [[v [s1 [e1 [A [C E]]]]]|R]; [left|right; exact R].
     exists v, s1, e1, (op "kl:_scm.assert-boolean" [v] s1). split; [exact A|]. split; [|exact E].
     rewrite evs_nil.
     change (conv (fun n => apply n p op "kl:_scm.assert-boolean" [v]) s1 (op "kl:_scm.assert-boolean" [v] s1)) with
       (evapp p op "kl:_scm.assert-boolean" [v] s1 (op "kl:_scm.assert-boolean" [v] s1)).
     rewrite (evapp_op p op _ _ s1 _ Pf). subst o. split; [apply B.completed_after in C; exact C|reflexivity]. }
 assert (BOOL : forall v, (exists bb, v = Boolean bb) \/ (forall bb, v <> Boolean bb)).
 { intros [| | | | | |bb| | |]; try (right; intros bb' X; discriminate X). left; exists bb; reflexivity. }
 rewrite ev_if. split.
 - intros [[w [s2 [e2 [o3 [T [B E]]]]]]|[T S]].
   + apply CALL in T. destruct T as [[v [s1 [e1 [A [C E1]]]]]|[_ S]]; [|exfalso; apply (S w); reflexivity].
     destruct (BOOL v) as [[bv V]|NB]; subst.
     * rewrite AT in E1. unfold after in E1; cbn in E1. inversion E1; subst. rewrite app_nil_r.
       left. exists bv, s1, e1, o3. split; [exact A|]. split; [destruct bv; exact B|reflexivity].
     * exfalso. pose proof (AF v s1 NB) as S. apply (S w).
       pose proof (f_equal answer E1) as X. cbn in X. exact (eq_sym X).
   + apply CALL in T. destruct T as [[v [s1 [e1 [A [C E1]]]]]|[A _]].
     * right; left. destruct (BOOL v) as [[bv V]|NB].
       -- subst. rewrite AT in S. exfalso. apply (S (Boolean bv)). reflexivity.
       -- exists v, s1, e1. tauto.
     * right; right. tauto.
 - intros [[bv [s1 [e1 [o2 [A [B E]]]]]]|[[v [s1 [e1 [NB [A [C E]]]]]]|[A S]]].
   + left. exists (Boolean bv), s1, (e1 ++ [])%list, o2. split.
     * apply (proj2 (CALL _)). left. exists (Boolean bv), s1, e1. split; [exact A|]. rewrite AT.
       split; [apply returned_completed|reflexivity].
     * split; [destruct bv; exact B|]. subst out. unfold after. rewrite app_nil_r. reflexivity.
   + right. split; [apply (proj2 (CALL _)); left; exists v, s1, e1; tauto|].
     subst out. intros w X. pose proof (AF v s1 NB) as S. apply (S w). cbn in X. exact X.
   + right. split; [apply (proj2 (CALL _)); right; tauto|exact S].
Qed.

Lemma elements_inv : forall v xs, elements v = Some xs -> v = L xs.
Proof.
 induction v as [| | | | | | |a _ b IH| |]; intros xs E; cbn in E; try discriminate.
 - inversion E; reflexivity.
 - destruct (elements b) as [ys|] eqn:Eb; [|discriminate]. inversion E; subst. cbn. rewrite (IH ys eq_refl). reflexivity.
Qed.
Lemma dcases_cons : forall d c cs, D.dcases d (c :: cs) = match elements c with
   | Some [Boolean true;b] => match cs with [] => d b | _ => None end
   | Some [c;b] => match d c, d b, D.dcases d cs with
     | Some c, Some b, Some rest => Some (If c b rest) | _,_,_ => None end
   | _ => None end.
Proof. reflexivity. Qed.
Lemma dcases_no_true : forall d cs, (forall b, ~ In (L [Boolean true; b]) cs) -> D.dcases d cs = None.
Proof.
 intros d cs; induction cs as [|c cs IH]; intro H; [reflexivity|]. rewrite dcases_cons.
 rewrite IH by (intros b' I; apply (H b'); right; exact I).
 destruct (elements c) as [l|] eqn:E; [|reflexivity].
 destruct l as [|x [|b [|y l]]]; try reflexivity;
  (destruct x as [| | | | | |[|]| | |]; try reflexivity; try (destruct (d _), (d b); reflexivity)).
 exfalso. apply (H b). left. exact (elements_inv _ _ E).
Qed.
(* The emitted cond (emit-cond: `cond` consed onto the compiled clauses) is
   read by the Scheme reader only when a clause test is the literal #t. With
   no such clause the reader rejects it at EVERY budget: no preservation is
   claimed there. Natively Shen-Scheme returns #<void> while the KLambda
   profile raises XCondFail (sampled counterexample,
   tests/scheme-compose.shen cond-no-true-clause-falls-through). *)
Theorem cond_without_true_unread : forall n clauses, (forall b, ~ In (L [Boolean true; b]) clauses) ->
 decode n (Pair (Symbol "cond") (L clauses)) = None.
Proof.
 intros [|n] clauses H; [reflexivity|].
 change (Pair (Symbol "cond") (L clauses)) with (L (Symbol "cond" :: clauses)).
 cbn [decode]. rewrite elements_list. cbn -[decode]. rewrite D.cases_inline. apply dcases_no_true; exact H.
Qed.

(* ---------- 3. equality ---------- *)
(* eqv? and kl:= agree on exact integers ... *)
Lemma eqv_exact_agrees : forall n m,
 primitive "eqv?" [Integer n; Integer m] = Some (Boolean (Z.eqb n m)) /\ B.kleq (Integer n) (Integer m) = Some (Z.eqb n m).
Proof. split; reflexivity. Qed.
(* ... and the model makes NO claim for mixed exactness (native disagreement:
   tests/scheme-compose.shen eqv-literal-mixed-exactness-counterexample). *)
Lemma eqv_mixed_unmodelled : forall n t,
 primitive "eqv?" [Integer n; Inexact t] = None /\ B.kleq (Integer n) (Inexact t) = None.
Proof. split; reflexivity. Qed.

Lemma eqv_not_keyword : ~ In "eqv?" D.keywords.
Proof. cbn. intuition discriminate. Qed.

(* The numeric branch composed with the captured ordering pass: when a
   literal number occurs (and neither side is an unbound symbol or [fail]),
   every successful run of the captured emit-equality-check yields syntax
   that, through the captured order-call, is read as a target with exactly
   the outcomes, state and trace of (eqv? d1 d2) on the compiled operands.
   The order-call call is any implementation whose completed outcomes are
   outcomes of the captured pass (its Wave-A world). *)
Theorem numeric_equality_preserves : forall cexp ordc ext ys1 ys2 gen N v1 v2 s u1 u2 d1 d2 st r st' tr,
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1) ->
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2) ->
 (u1 || u2 || B.is_fail v1 || B.is_fail v2) = false -> (numeric v1 || numeric v2) = true ->
 (forall c st o, ordc c st = o -> completed o -> evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [c] st o) ->
 (forall st' c st'' t, cexp v1 s st' = Out (Returned c) st'' t -> decode N c = Some d1 /\ Pre.no_lambda c) ->
 (forall st' c st'' t, cexp v2 s st' = Out (Returned c) st'' t -> decode N c = Some d2 /\ Pre.no_lambda c) ->
 evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.emit-equality-check" [v1; v2; s] st (Out (Returned r) st' tr) ->
 exists target, decode (S (S N)) r = Some target /\
  forall p op rho st out, Pre.bound_args rho [d1; d2] ->
   (ev p op rho (Call "eqv?" [d1; d2]) st out <-> ev p op rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 gen N v1 v2 s u1 u2 d1 d2 st r st' tr U1 U2 C1 C2 OS D1 D2 H.
 apply (B.emit_equality_exact cexp ordc ext ys1 ys2 v1 v2 s u1 u2 U1 U2 st) in H. destruct H as [_ E].
 unfold B.emit_eq_spec in E. rewrite C1, C2 in E. unfold B.eq_call, bind in E.
 destruct (cexp v1 s st) as [[c1| | |] s1 e1] eqn:X1; cbn in E; try discriminate E.
 destruct (cexp v2 s s1) as [[c2| | |] s2 e2] eqn:X2; cbn in E; try discriminate E.
 destruct (ordc (Pair (Symbol "eqv?") (Pair c1 (Pair c2 Nil))) s2) as [ro so to] eqn:O; cbn in E.
 injection E as Ero Eso Etr; subst ro so.
 destruct (D1 _ _ _ _ X1) as [E1 N1]. destruct (D2 _ _ _ _ X2) as [E2 N2].
 assert (Ev : evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L [Symbol "eqv?"; c1; c2]] s2 (Out (Returned r) st' to)).
 { apply OS; [exact O|apply returned_completed]. }
 assert (Dc : decode (S N) (L (Symbol "eqv?" :: [c1; c2])) = Some (Call "eqv?" [d1; d2])).
 { rewrite (D.decode_call N "eqv?" [c1; c2] eqv_not_keyword). cbn [D.dmany]. rewrite E1, E2. reflexivity. }
 destruct (Pre.order_call_preserves gen N "eqv?" [c1; c2] [d1; d2] s2 r st' to eqv_not_keyword Dc
   (Forall_cons _ N1 (Forall_cons _ N2 (Forall_nil _))) Ev) as [target [DT EQ]].
 exists target. split; [exact DT|exact EQ].
Qed.
End SchemeCompose.
