(* Port-fix lane: the PATCHED Shen-Scheme conditional and equality emitters.

   Capture: CompilerBranchesPatchedInput, the eight compiler-branch defines of
   tizoc/shen-scheme src/compiler.shen 8d261518 with
   ports/patches/shen-scheme-compiler.diff applied (packaging:
   scripts/package-patched.py, patch sha256 and patched blob pinned). This is
   NOT the stock port: every stock theorem (SchemeBranches, SchemeCompose)
   and the refuted stock obligations are unchanged.

   The world is the stock one (SchemeBranches.op): recursive
   compile-expression, the order-call call and every uncaptured compiler
   function (unbound-symbol?, prefix-op, ...) are ARBITRARY operations, and
   every theorem holds for all of them. Evidence kind: universal theorems
   about the captured patched definitions. *)
From Coq Require Import List String ZArith Bool Ascii Arith Lia.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep DecodeFacts
  CallRefinement OrderCallInput OrderCallPass OrderCallPreserve CompilerBranchesPatchedInput
  KernelElementInput SchemeBranches SchemeCompose.
Import ListNotations.
Module SchemePatched.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module B := SchemeBranches.SchemeBranches.
Module D := DecodeFacts.DecodeFacts.
Module Pass := OrderCallPass.OrderCallPass.
Module Pre := OrderCallPreserve.OrderCallPreserve.
Open Scope string_scope.

(* The linked patched world: the patched branch capture, the captured
   merge-nested-lets and the captured kernel element?, linked as in stock. *)
Definition linked := (compiler_branches_patched_program ++ firstn 1 order_call_program ++ kernel_element_program)%list.
Definition P : program := fun name => lookup linked (B.link name).

Section World.
Variable cexp : value -> value -> computation.
Variable ordc : value -> computation.
Variable ext : string -> list value -> computation.
Variables ys1 ys2 : list string.
Definition op := B.op cexp ordc ext ys1 ys2.

Definition returns f vs v := forall st, evapp P op f vs st (Out (Returned v) st []).
Lemma returns_def : forall f vs d v, P f = Some d -> List.length (params d) = List.length vs ->
 yields P op (arguments (params d) vs) (body d) v -> returns f vs v.
Proof. intros f vs d v Df A Y st. apply (evapp_def P op f vs d st _ Df A). apply Y. Qed.
Lemma returns_prim : forall f vs v, P f = None -> (forall st, op f vs st = Out (Returned v) st []) -> returns f vs v.
Proof. intros f vs v Df O st. apply (evapp_op P op f vs st _ Df). split; [apply returned_completed|apply O]. Qed.
Lemma yields_call_returns : forall rho f es vs v, Forall2 (yields P op rho) es vs -> returns f vs v ->
 yields P op rho (Call f es) v.
Proof. intros rho f es vs v F R. exact (yields_returns P op rho f es vs v F R). Qed.
Lemma op_kleq : forall a b r st, B.kleq a b = Some r -> op "kl:=" [a; b] st = Out (Returned (Boolean r)) st [].
Proof. exact (B.op_kleq cexp ordc ext ys1 ys2). Qed.
Lemma op_eq_symbol : forall s h st, op "eq?" [Symbol s; h] st = Out (Returned (Boolean (B.head_is s h))) st [].
Proof. exact (B.op_eq_symbol cexp ordc ext ys1 ys2). Qed.
(* kl:= against the literal true: the Boolean answer, kept folded. *)
Definition is_btrue v := match v with Boolean y => Bool.eqb true y | _ => false end.
Arguments is_btrue !v.
Lemma kleq_true : forall v, B.kleq (Boolean true) v = Some (is_btrue v).
Proof. reflexivity. Qed.
(* null? on an abstract value, kept folded as B.is_nil. *)
Lemma op_null : forall v st, op "null?" [v] st = Out (Returned (Boolean (B.is_nil v))) st [].
Proof. intros [| | | | | | | | |] st; reflexivity. Qed.
Lemma is_btrue_true : forall v, is_btrue v = true -> v = Boolean true.
Proof. intros [| | | | | |[|]| | |] H; try discriminate H; reflexivity. Qed.

(* The selection and evaluation tactics of SchemeBranches, for this world. *)
Ltac decisions := repeat match goal with Q : _ = true |- _ => rewrite Q | Q : _ = false |- _ => rewrite Q end.
Ltac sel := cbn [is_btrue]; cbv beta iota zeta fix delta [L fold_right map negb andb orb]; decisions;
 cbn [String.eqb Ascii.eqb Bool.eqb]; cbv beta iota zeta fix delta [L fold_right map negb andb orb].
Ltac Y := match goal with
 | |- yields _ _ _ (Lit _) _ => apply yields_lit
 | |- yields _ _ _ (Var _) _ => apply yields_var; reflexivity
 | |- yields _ _ _ (If _ _ _) _ => eapply yields_if; [Y|sel; Y]
 | |- yields _ _ _ (And _ _) _ => eapply yields_and; [Y|sel; Y]
 | |- yields _ _ _ (Or _ _) _ => eapply yields_or; [Y|sel; Y]
 | |- yields _ _ _ (Let _ _ _) _ => eapply yields_let; [Y|Y]
 | |- yields _ _ _ (Call _ _) _ => eapply yields_call_returns; [Yargs|R]
 end
with R := first
 [ match goal with |- returns ?f _ _ => first
     [ match goal with H : returns f _ _ |- _ => apply H end
     | match goal with H : forall _, returns f _ _ |- _ => apply H end
     | match goal with H : forall _ _, returns f _ _ |- _ => apply H end ] end
 | match goal with |- returns "kl:=" [Boolean true; _] _ =>
     eapply returns_prim; [reflexivity|intro; apply op_kleq; apply kleq_true] end
 | match goal with |- returns "null?" [?v] _ => is_var v;
     eapply returns_prim; [reflexivity|intro; apply op_null] end
 | eapply returns_prim; [reflexivity|intro; reflexivity]
 | match goal with |- returns "kl:=" _ _ =>
     eapply returns_prim; [reflexivity|intro; apply op_kleq;
       first [apply B.kleq_symbol|apply B.kleq_fail|apply kleq_true]] end
 | match goal with |- returns "eq?" _ _ => eapply returns_prim; [reflexivity|intro; apply op_eq_symbol] end
 | eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Y] ]
with Yargs := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [Y|Yargs]
 end.
Ltac body := eapply returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]].

Lemma kernel_element_returns : forall x ys,
 returns "kl:buri.kernel.element?" [x; L (map Symbol ys)] (Boolean (B.member x ys)).
Proof.
 intros x ys; induction ys as [|t ys IH]; [body; Y|].
 unfold B.member; cbn [map existsb]; fold (B.member x ys).
 destruct (B.name_is t x) eqn:Q; cbn [orb]; body; Y.
Qed.
Lemma element_returns : forall x ys, returns "kl:element?" [x; L (map Symbol ys)] (Boolean (B.member x ys)).
Proof. intros x ys st. exact (kernel_element_returns x ys st). Qed.
Definition yields_b := B.yields_b ys1 ys2.
Definition force_spec := B.force_spec ys1 ys2.
Lemma yields_returns : forall v, returns "kl:_scm.yields-boolean?" [v] (Boolean (yields_b v)).
Proof.
 assert (EL := element_returns). assert (EQ := op_eq_symbol). unfold yields_b.
 fix IH 1. intro v.
 destruct v as [| | | | | |[|]|h t| |]; try (body; Y).
 destruct (B.head_is "let" h) eqn:Ql; destruct (B.head_is "do" h) eqn:Qd;
 (destruct t as [| | | | | | |a t2| |]; [| | | | | | |destruct t2 as [| | | | | | |b t3| |]| |]);
 try (destruct t3 as [| | | | | | |e t4| |]; [| | | | | | |destruct t4| |]);
 cbn [B.yields_b]; decisions; cbn [andb]; body; Y.
Qed.
Lemma force_returns : forall v, returns "kl:_scm.force-boolean" [v] (force_spec v).
Proof.
 intro v. assert (YR := yields_returns). unfold force_spec, B.force_spec. fold (yields_b v).
 destruct (yields_b v) eqn:Q; body; Y.
Qed.

Ltac Dn := match goal with
 | |- B.denotes _ _ _ (Lit _) _ => apply B.denotes_lit
 | |- B.denotes _ _ _ (Var _) _ => apply B.denotes_yields; apply yields_var; reflexivity
 | |- B.denotes _ _ _ (If _ _ _) _ => eapply B.denotes_if_yields; [Y|sel; Dn]
 | |- B.denotes _ _ _ (Let _ _ _) _ => eapply B.denotes_let; [Dn|intro; Dn]
 | |- B.denotes _ _ _ (Call _ _) _ => first [eapply B.denotes_call_pure; [Yargs|DA] | eapply B.denotes_call; [Ds|intro; DA]]
 end
with Ds := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [Dn|Ds]
 end
with DA := first
 [ match goal with |- B.denotes_app _ _ ?f _ _ => first
     [ match goal with H : B.denotes_app _ _ f _ _ |- _ => apply H end
     | match goal with H : forall _, B.denotes_app _ _ f _ _ |- _ => apply H end ] end
 | apply B.denotes_app_op; reflexivity
 | eapply B.denotes_app_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Dn] ].
Ltac start := eapply B.denotes_app_ext; [|eapply B.denotes_app_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Dn]].
Ltac finish_with stop := intro; cbv beta iota zeta delta -[app stop]; repeat (match goal with
 | |- context [cexp ?x ?y ?z] => destruct (cexp x y z) as [[| | |] ? ?]
 | |- context [ordc ?x ?z] => destruct (ordc x z) as [[| | |] ? ?]
 | |- context [ext ?x ?y ?z] => destruct (ext x y z) as [[| | |] ? ?]
 end; cbv beta iota zeta delta -[app stop]); cbn [app]; rewrite ?app_nil_r, ?app_assoc; reflexivity.

(* ---------- 1. cond ---------- *)
Definition err_form := L [Symbol "simple-error"; Text "condition failure"].
Fixpoint pclauses_spec cs s : computation := match cs with
 | Nil => bind (cexp err_form s) (fun e => ret (L [L [Boolean true; e]]))
 | Pair (Pair t (Pair b Nil)) rest =>
   if is_btrue t && B.is_nil rest then bind (cexp b s) (fun cb => ret (L [L [Boolean true; cb]]))
   else bind (cexp (force_spec t) s) (fun ct => bind (cexp b s) (fun cb =>
     bind (pclauses_spec rest s) (fun cr => ret (Pair (L [ct; cb]) cr))))
 | _ => ext "kl:shen.f-error" [Symbol "_scm.emit-cond-clauses"] end.
(* Exact denotation of the patched emit-cond-clauses: an empty clause list
   compiles (simple-error "condition failure") into a final #t clause; a final
   literal-true clause compiles only its body; every other clause is compiled
   as in stock (forced test, then body, then the rest). *)
Definition wf_tail tl := match tl with Pair _ Nil => True | _ => False end.
Lemma cell_malformed : forall t tl rest s, ~ wf_tail tl ->
 B.denotes_app P op "kl:_scm.emit-cond-clauses" [Pair (Pair t tl) rest; s] (pclauses_spec (Pair (Pair t tl) rest) s).
Proof.
 intros t tl rest s W. assert (FR := force_returns).
 destruct (is_btrue t) eqn:Q;
  (destruct tl as [| | | | | | |b [| | | | | | | | |]| |];
   [> try (exfalso; apply W; exact I) ..];
   start; cbn [pclauses_spec]; finish_with pclauses_spec).
Qed.
Lemma cell_wf : forall t b rest s, B.denotes_app P op "kl:_scm.emit-cond-clauses" [rest; s] (pclauses_spec rest s) ->
 B.denotes_app P op "kl:_scm.emit-cond-clauses" [Pair (Pair t (Pair b Nil)) rest; s]
  (pclauses_spec (Pair (Pair t (Pair b Nil)) rest) s).
Proof.
 intros t b rest s IH. assert (FR := force_returns).
 destruct (is_btrue t) eqn:Q; destruct (B.is_nil rest) eqn:Nr;
 start; cbn [pclauses_spec]; rewrite ?Q, ?Nr; cbn [andb]; finish_with pclauses_spec.
Qed.
Theorem patched_emit_cond_clauses_exact : forall cs s,
 B.denotes_app P op "kl:_scm.emit-cond-clauses" [cs; s] (pclauses_spec cs s).
Proof.
 intros cs s. assert (FR := force_returns).
 induction cs as [| | | | | | |c _ rest IH| |]; try (start; cbn [pclauses_spec]; finish_with force_spec).
 destruct c as [| | | | | | |t tl| |]; try (start; cbn [pclauses_spec]; finish_with pclauses_spec).
 destruct tl as [| | | | | | |b [| | | | | | | | |]| |];
  first [apply cell_wf; exact IH | apply cell_malformed; cbn [wf_tail]; tauto].
Qed.
Theorem patched_emit_cond_exact : forall cs s, B.denotes_app P op "kl:_scm.emit-cond" [cs; s]
 (bind (pclauses_spec cs s) (fun r => ret (Pair (Symbol "cond") r))).
Proof.
 intros cs s. assert (C := patched_emit_cond_clauses_exact cs s). start.
 intro st. cbv beta iota zeta delta -[app pclauses_spec]. destruct (pclauses_spec cs s st) as [[| | |] ? ?];
 cbv beta iota zeta delta -[app pclauses_spec]; rewrite ?app_nil_r; reflexivity.
Qed.

(* A source clause list with no literal-true test. *)
Fixpoint no_true (cs : value) : Prop := match cs with
 | Nil => True
 | Pair (Pair t (Pair _ Nil)) rest => t <> Boolean true /\ no_true rest
 | _ => False end.
Definition produced (m : computation) v := exists st1 st2 tr, m st1 = Out (Returned v) st2 tr.
Definition compiled_clause s c := exists t ct cb b, c = L [ct; cb] /\ t <> Boolean true /\
 produced (cexp (force_spec t) s) ct /\ produced (cexp b s) cb.

Lemma pclauses_no_true : forall cs s st r st' tr, no_true cs ->
 pclauses_spec cs s st = Out (Returned r) st' tr ->
 exists pre fin, r = L (pre ++ [L [Boolean true; fin]]) /\ produced (cexp err_form s) fin /\
  Forall (compiled_clause s) pre.
Proof.
 induction cs as [|x1|x2|x3|x4 x5|x6|x7|c _ rest IH|x8|x9]; intros s st r st' tr NT H; try contradiction.
 - cbn [pclauses_spec] in H. unfold bind, ret, return_result in H.
   destruct (cexp err_form s st) as [[e| | |] s1 e1] eqn:E; cbn in H; try discriminate H.
   injection H as <- _ _. exists [], e. split; [reflexivity|]. split; [exists st, s1, e1; exact E|constructor].
 - destruct c as [| | | | | | |t [| | | | | | |b [| | | | | | | | |]| |]| |]; try contradiction.
   destruct NT as [Nt NR].
   assert (G : pclauses_spec (Pair (Pair t (Pair b Nil)) rest) s =
     bind (cexp (force_spec t) s) (fun ct => bind (cexp b s) (fun cb =>
       bind (pclauses_spec rest s) (fun cr => ret (Pair (L [ct; cb]) cr))))).
   { cbn [pclauses_spec]. destruct (is_btrue t) eqn:Q; [exfalso; apply Nt; apply is_btrue_true; exact Q|reflexivity]. }
   rewrite G in H. clear G. unfold bind, ret, return_result in H.
   destruct (cexp (force_spec t) s st) as [[ct| | |] s1 e1] eqn:E1; cbn in H; try discriminate H.
   destruct (cexp b s s1) as [[cb| | |] s2 e2] eqn:E2; cbn in H; try discriminate H.
   destruct (pclauses_spec rest s s2) as [[cr| | |] s3 e3] eqn:E3; cbn in H; try discriminate H.
   injection H as <- _ _.
   destruct (IH s s2 cr s3 e3 NR E3) as [pre [fin [-> [F A]]]].
   exists (L [ct; cb] :: pre), fin. split; [reflexivity|]. split; [exact F|].
   constructor; [|exact A]. exists t, ct, cb, b. split; [reflexivity|]. split; [exact Nt|].
   split; [exists st, s1, e1; exact E1|exists s1, s2, e2; exact E2].
Qed.

(* For every source clause list with no literal-true test and every
   completed successful run of the captured patched emit-cond: the emitted
   form is a Scheme cond whose clauses are the compiled source clauses
   followed by a final #t clause holding a compilation of
   (simple-error "condition failure"). Contrast: the stock emitter has no
   final clause at all (SchemeCompose.cond_without_true_unread). *)
Theorem patched_cond_no_true : forall cs s st r st' tr, no_true cs ->
 evapp P op "kl:_scm.emit-cond" [cs; s] st (Out (Returned r) st' tr) ->
 exists pre fin, r = L (Symbol "cond" :: pre ++ [L [Boolean true; fin]]) /\
  produced (cexp err_form s) fin /\ Forall (compiled_clause s) pre.
Proof.
 intros cs s st r st' tr NT H. apply (patched_emit_cond_exact cs s st) in H. destruct H as [_ E].
 unfold bind, ret, return_result in E.
 destruct (pclauses_spec cs s st) as [[x| | |] s1 e1] eqn:X; cbn in E; try discriminate E.
 injection E as <- _ _. destruct (pclauses_no_true cs s st x s1 e1 NT X) as [pre [fin [-> R]]].
 exists pre, fin. split; [reflexivity|exact R].
Qed.

(* ---------- 2. numeric-literal equality ---------- *)
Definition peq_spec u1 u2 v1 v2 s :=
 if u1 || u2 || B.is_fail v1 || B.is_fail v2 then B.eq_call cexp ordc "eq?" v1 v2 s
 else if numeric v1 || numeric v2 then
   bind (ext "kl:_scm.prefix-op" [Symbol "="]) (fun h =>
   bind (cexp v1 s) (fun c1 => bind (cexp v2 s) (fun c2 => ordc (Pair h (L [c1; c2])))))
 else if B.is_text v1 || B.is_text v2 then B.eq_call cexp ordc "equal?" v1 v2 s
 else if B.is_nil v1 then B.null_call cexp v2 s
 else if B.is_nil v2 then B.null_call cexp v1 s
 else bind (ext "kl:_scm.native-mode" []) (fun m =>
   ext "kl:_scm.emit-static-application-fallback" [m; Symbol "="; L [v1; v2]; s]).
(* Exact branch selection of the patched emit-equality-check: identical to
   stock except the numeric-literal branch, which asks prefix-op for the
   name of =, then compiles V1, then V2, and hands the call to order-call. *)
Theorem patched_emit_equality_exact : forall v1 v2 s u1 u2,
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1) ->
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2) ->
 B.denotes_app P op "kl:_scm.emit-equality-check" [v1; v2; s] (peq_spec u1 u2 v1 v2 s).
Proof.
 intros v1 v2 s u1 u2 U1 U2.
 assert (R1 : returns "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1)).
 { apply returns_prim; [reflexivity|]. intro st. exact (U1 st). }
 assert (R2 : returns "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2)).
 { apply returns_prim; [reflexivity|]. intro st. exact (U2 st). }
 clear U1 U2. unfold peq_spec, B.eq_call, B.null_call.
 destruct u1; cbn [orb]; [start; finish_with app|].
 destruct u2; cbn [orb]; [start; finish_with app|].
 destruct (B.is_fail v1) eqn:F1; cbn [orb]; [start; finish_with app|].
 destruct (B.is_fail v2) eqn:F2; cbn [orb]; [start; finish_with app|].
 destruct (numeric v1) eqn:N1; cbn [orb]; [start; finish_with app|].
 destruct (numeric v2) eqn:N2; cbn [orb]; [start; finish_with app|].
 destruct (B.is_text v1) eqn:T1; unfold B.is_text in T1; cbn [orb]; [start; finish_with app|].
 destruct (B.is_text v2) eqn:T2; unfold B.is_text in T2; cbn [orb]; [start; finish_with app|].
 destruct v1 as [| | | | | | | | |]; cbn [B.is_nil]; try discriminate; [start; finish_with app| | | | |];
 (destruct v2 as [| | | | | | | | |]; cbn [B.is_nil]; try discriminate; start; finish_with app).
Qed.
End World.

(* An If chain whose final else-branch is E: (if c1 b1 (if c2 b2 ... E)). *)
Inductive falls : expr -> expr -> Prop :=
 | falls_end e : falls e e
 | falls_if c b r e : falls r e -> falls (If c b r) e.

Lemma dcases_tail : forall N pre fin E,
 Forall (fun c => exists ct cb ect ecb, c = L [ct; cb] /\ ct <> Boolean true /\
   decode N ct = Some ect /\ decode N cb = Some ecb) pre ->
 decode N fin = Some E ->
 exists tgt, D.dcases (decode N) (pre ++ [L [Boolean true; fin]]) = Some tgt /\ falls tgt E.
Proof.
 intros N pre fin E F DF. induction F as [|c pre [ct [cb [ect [ecb [-> [Nt [Dt Db]]]]]]] _ IH].
 - exists E. split; [cbn; rewrite DF; reflexivity|constructor].
 - destruct IH as [tgt [Dr Ft]]. exists (If ect ecb tgt). split; [|constructor; exact Ft].
   change ((L [ct; cb] :: pre) ++ [L [Boolean true; fin]])%list with (L [ct; cb] :: (pre ++ [L [Boolean true; fin]]))%list.
   rewrite SchemeCompose.SchemeCompose.dcases_cons, elements_list.
   destruct ct as [| | | | | |[|]| | |]; try (exfalso; apply Nt; reflexivity);
   cbv beta iota; rewrite Dt, Db, Dr; reflexivity.
Qed.

(* Reading: whenever every compiled clause part is read by the Scheme reader
   at budget N, compiled tests of non-literal-true source tests are not the
   literal #t, and the compiled (simple-error "condition failure") is read as
   E, the patched cond IS read, at budget N+1, as the KLambda reduction
   (if T1 B1 (if T2 B2 ... E)) — the porting rule (cond) = (simple-error
   "condition failure") — for every source clause list without a
   literal-true test. *)
Theorem patched_cond_reads : forall cexp ordc ext ys1 ys2 cs s st r st' tr N E, no_true cs ->
 evapp P (op cexp ordc ext ys1 ys2) "kl:_scm.emit-cond" [cs; s] st (Out (Returned r) st' tr) ->
 (forall t ct, t <> Boolean true -> produced (cexp (force_spec ys1 ys2 t) s) ct ->
    ct <> Boolean true /\ exists e, decode N ct = Some e) ->
 (forall b cb, produced (cexp b s) cb -> exists e, decode N cb = Some e) ->
 (forall fin, produced (cexp err_form s) fin -> decode N fin = Some E) ->
 exists tgt, decode (S N) r = Some tgt /\ falls tgt E.
Proof.
 intros cexp ordc ext ys1 ys2 cs s st r st' tr N E NT H HT HB HE.
 destruct (patched_cond_no_true cexp ordc ext ys1 ys2 cs s st r st' tr NT H) as [pre [fin [-> [PF A]]]].
 assert (F : Forall (fun c => exists ct cb ect ecb, c = L [ct; cb] /\ ct <> Boolean true /\
   decode N ct = Some ect /\ decode N cb = Some ecb) pre).
 { eapply Forall_impl; [|exact A]. intros c [t [ct [cb [b [-> [Nt [Pt Pb]]]]]]].
   destruct (HT t ct Nt Pt) as [Nc [ect Et]]. destruct (HB b cb Pb) as [ecb Eb].
   exists ct, cb, ect, ecb. auto. }
 destruct (dcases_tail N pre fin E F (HE fin PF)) as [tgt [Dt Ft]].
 exists tgt. split; [|exact Ft].
 cbn [decode]. rewrite elements_list. cbn -[decode]. rewrite D.cases_inline. exact Dt.
Qed.

Lemma kleq_not_keyword : ~ In "kl:=" D.keywords.
Proof. cbn. intuition discriminate. Qed.

(* The patched numeric branch composed with the captured ordering pass: when
   a literal number occurs (and neither side is an unbound symbol or [fail]),
   and prefix-op names = as kl:= (its upstream definition concatenates
   *kl-prefix* "kl:"; it is uncaptured, so this is a stated premise), every
   successful run of the captured patched emit-equality-check yields syntax
   read as a target with exactly the outcomes, state and trace of the call
   (kl:= d1 d2) on the compiled operands, for every program, operation table
   and environment. So the literal path IS the kl:= path: it agrees with kl:=
   on every pair of values, including numerically equal values of different
   exactness, whatever numeric profile kl:= has. *)
Theorem patched_numeric_equality_is_kleq : forall cexp ordc ext ys1 ys2 gen N v1 v2 s u1 u2 d1 d2 st r st' tr,
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v1; s] (Boolean u1) ->
 B.pure_answer ext "kl:_scm.unbound-symbol?" [v2; s] (Boolean u2) ->
 B.pure_answer ext "kl:_scm.prefix-op" [Symbol "="] (Symbol "kl:=") ->
 (u1 || u2 || B.is_fail v1 || B.is_fail v2) = false -> (numeric v1 || numeric v2) = true ->
 (forall c st o, ordc c st = o -> completed o -> evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [c] st o) ->
 (forall st' c st'' t, cexp v1 s st' = Out (Returned c) st'' t -> decode N c = Some d1 /\ Pre.no_lambda c) ->
 (forall st' c st'' t, cexp v2 s st' = Out (Returned c) st'' t -> decode N c = Some d2 /\ Pre.no_lambda c) ->
 evapp P (op cexp ordc ext ys1 ys2) "kl:_scm.emit-equality-check" [v1; v2; s] st (Out (Returned r) st' tr) ->
 exists target, decode (S (S N)) r = Some target /\
  forall p op rho st out, Pre.bound_args rho [d1; d2] ->
   (ev p op rho (Call "kl:=" [d1; d2]) st out <-> ev p op rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 gen N v1 v2 s u1 u2 d1 d2 st r st' tr U1 U2 PO C1 C2 OS D1 D2 H.
 apply (patched_emit_equality_exact cexp ordc ext ys1 ys2 v1 v2 s u1 u2 U1 U2 st) in H. destruct H as [_ E].
 unfold peq_spec in E. rewrite C1, C2 in E. unfold bind in E. rewrite (PO st) in E. cbn in E.
 destruct (cexp v1 s st) as [[c1| | |] s1 e1] eqn:X1; cbn in E; try discriminate E.
 destruct (cexp v2 s s1) as [[c2| | |] s2 e2] eqn:X2; cbn in E; try discriminate E.
 destruct (ordc (Pair (Symbol "kl:=") (Pair c1 (Pair c2 Nil))) s2) as [ro so to] eqn:O; cbn in E.
 injection E as Ero Eso Etr; subst ro so.
 destruct (D1 _ _ _ _ X1) as [E1 N1]. destruct (D2 _ _ _ _ X2) as [E2 N2].
 assert (Ev : evapp Pass.P (Pass.op gen) "kl:_scm.order-call" [L [Symbol "kl:="; c1; c2]] s2 (Out (Returned r) st' to)).
 { apply OS; [exact O|apply returned_completed]. }
 assert (Dc : decode (S N) (L (Symbol "kl:=" :: [c1; c2])) = Some (Call "kl:=" [d1; d2])).
 { rewrite (D.decode_call N "kl:=" [c1; c2] kleq_not_keyword). cbn [D.dmany]. rewrite E1, E2. reflexivity. }
 destruct (Pre.order_call_preserves gen N "kl:=" [c1; c2] [d1; d2] s2 r st' to kleq_not_keyword Dc
   (Forall_cons _ N1 (Forall_cons _ N2 (Forall_nil _))) Ev) as [target [DT EQ]].
 exists target. split; [exact DT|exact EQ].
Qed.
End SchemePatched.
