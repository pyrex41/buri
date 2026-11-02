(* Progress of the actual captured Shen-Scheme argument-ordering pass with the
   real counter-based gensym, and the unconditional composed preservation
   theorems (E2E-15).

   gensym is no longer arbitrary here: [counter] is the stated contract of
   Shen kernel 43.1 sys.shen (pinned ports/upstream/sys.shen, lines 108-112)
     gensym Sym = concat Sym (set G (+ 1 (value G))), G the global gensym counter,
     concat S1 S2 = intern (cn (str S1) (str S2)),
   with the evaluator state holding the value of that counter (a static
   global of the compiler) and [str] of an integer its decimal spelling. That
   the boot image's compiled gensym, str and intern behave so is a contract,
   not a theorem (the same contract boundary as the rest of the pass).

   Termination argument: decimal spellings are injective, so the generated
   names arg(z+1), arg(z+2), ... are pairwise distinct; the used syntax
   contains finitely many symbol names, so among the next (#names + 1)
   candidates one is absent (pigeonhole) and the fresh loop returns it; the
   input loop is structural on the argument list. All theorems are universal
   over the starting counter value and the input call. *)
From Coq Require Import List String ZArith Bool Arith Lia DecimalString DecimalPos DecimalZ.
From Buri Require Import Native ObserverEffects EffectContract EffectBigStep DecodeFacts
  OrderCallCorrect OrderCallPass OrderCallPreserve SchemeBranches SchemeCompose.
Import ListNotations.
Module OrderCallProgress.
Import Native.Native ObserverEffects.ObserverEffects EffectContract.EffectContract EffectBigStep.EffectBigStep.
Module O := OrderCallCorrect.OrderCallCorrect.
Module D := DecodeFacts.DecodeFacts.
Module Pass := OrderCallPass.OrderCallPass.
Module Pre := OrderCallPreserve.OrderCallPreserve.
Module B := SchemeBranches.SchemeBranches.
Module C := SchemeCompose.SchemeCompose.
Open Scope string_scope.

(* ---------- the counter-based generator ---------- *)
Definition gname (z : Z) := ("arg" ++ spelling z)%string.
Definition counter : computation := fun st => match st with
 | Integer z => Out (Returned (Symbol (gname (z + 1)))) (Integer (z + 1)) []
 | _ => Out Unsupported st [] end.

Lemma spelling_inj : forall a b, spelling a = spelling b -> a = b.
Proof.
 assert (NN : forall z, Z.to_int z <> Decimal.Pos Decimal.Nil /\ Z.to_int z <> Decimal.Neg Decimal.Nil).
 { intros [|p|p]; cbn; split; try discriminate; intro E; injection E as E;
   exact (DecimalPos.Unsigned.to_uint_nonnil p E). }
 intros a b E. unfold spelling in E.
 assert (F := f_equal NilZero.int_of_string E).
 destruct (NN a) as [A1 A2]. destruct (NN b) as [B1 B2].
 rewrite (NilZero.isi _ A1 A2), (NilZero.isi _ B1 B2) in F. injection F as F.
 rewrite <- (DecimalZ.of_to a), <- (DecimalZ.of_to b), F. reflexivity.
Qed.
Lemma gname_inj : forall a b, gname a = gname b -> a = b.
Proof. intros a b E. unfold gname in E. cbn in E. injection E as E. exact (spelling_inj _ _ E). Qed.

(* ---------- finitely many names occur ---------- *)
Fixpoint syms v := match v with Symbol s => [s] | Pair a b => (syms a ++ syms b)%list | _ => [] end.
Lemma occ_in : forall name v, O.occurrences name v <> 0 -> In name (syms v).
Proof.
 intros name v; induction v; cbn [O.occurrences syms]; intro H; try lia.
 - destruct (String.eqb name s) eqn:E; [|lia]. apply String.eqb_eq in E. left; symmetry; exact E.
 - apply in_or_app. destruct (O.occurrences name v1); [right; apply IHv2; lia|left; apply IHv1; lia].
Qed.
Lemma nodup_map_inj : forall (f : nat -> string) l, (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
 intros f l I N; induction N as [|x l X N IH]; cbn; constructor; [|exact IH].
 intro M. apply in_map_iff in M as [y [E Y]]. apply I in E; subst. contradiction.
Qed.
Lemma forallb_false_witness : forall (A : Type) (f : A -> bool) l, forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
 intros A f l; induction l as [|a l IH]; cbn; [discriminate|].
 destruct (f a) eqn:F; cbn; intro H; [destruct (IH H) as [x [I X]]; exists x; auto|exists a; auto].
Qed.
(* Pigeonhole: one of the next (#names + 1) generated names does not occur. *)
Theorem absent_candidate : forall u z, exists d, d <= List.length (syms u) /\
 O.occurrences (gname (z + Z.of_nat (S d))) u = 0.
Proof.
 intros u z. set (m := List.length (syms u)).
 set (cand := fun d => gname (z + Z.of_nat (S d))).
 set (names := map cand (seq 0 (S m))).
 assert (ND : NoDup names).
 { apply nodup_map_inj; [|apply seq_NoDup]. intros x y E. apply gname_inj in E. lia. }
 destruct (forallb (fun s => existsb (String.eqb s) (syms u)) names) eqn:F.
 - exfalso. assert (I : incl names (syms u)).
   { intros s S. rewrite forallb_forall in F. specialize (F s S). apply existsb_exists in F as [t [T E]].
     apply String.eqb_eq in E; subst; exact T. }
   pose proof (NoDup_incl_length ND I) as Len. unfold names in Len. rewrite map_length, seq_length in Len. lia.
 - destruct (forallb_false_witness _ _ _ F) as [s [S E]].
   unfold names in S. apply in_map_iff in S as [d [Ed Sd]]. apply in_seq in Sd.
   exists d. split; [lia|]. fold (cand d). rewrite Ed.
   destruct (O.occurrences s u) eqn:Oc; [reflexivity|exfalso].
   assert (In s (syms u)) as Is by (apply occ_in; lia).
   assert (existsb (String.eqb s) (syms u) = true) as T by (apply existsb_exists; exists s; split; [exact Is|apply String.eqb_refl]).
   congruence.
Qed.

(* ---------- stateful evaluation steps ---------- *)
Section Steps.
Variable p : program.
Variable op : string -> list value -> computation.
Lemma ev_let_state : forall rho s a b st v s1 out, ev p op rho a st (Out (Returned v) s1 []) ->
 ev p op (Native.bind rho s v) b s1 out -> ev p op rho (Let s a b) st out.
Proof.
 intros rho s a b st v s1 out A Bd. apply ev_let. left. exists v, s1, [], out.
 split; [exact A|]. split; [exact Bd|symmetry; apply after_nil].
Qed.
Lemma ev_let_state_inv : forall rho s a b st v s1 out, ev p op rho a st (Out (Returned v) s1 []) ->
 ev p op rho (Let s a b) st out -> ev p op (Native.bind rho s v) b s1 out.
Proof.
 intros rho s a b st v s1 out A H. apply ev_let in H.
 destruct H as [[v' [s' [e' [o [A' [Bd E]]]]]]|[A' S]].
 - pose proof (ev_det p op _ _ _ _ _ A A') as X. inversion X; subst. rewrite after_nil. exact Bd.
 - pose proof (ev_det p op _ _ _ _ _ A A') as X. subst out. exfalso; apply (S v); reflexivity.
Qed.
Lemma ev_focus_state : forall rho f pre a post vpre vpost st v s1 out,
 Forall2 (yields p op rho) pre vpre -> Forall2 (yields p op rho) post vpost ->
 ev p op rho a st (Out (Returned v) s1 []) -> evapp p op f (vpre ++ v :: vpost) s1 out ->
 ev p op rho (Call f (pre ++ a :: post)) st out.
Proof.
 intros rho f pre a post vpre vpost st v s1 out Pr Po A F.
 apply (proj2 (ev_call_focus p op rho f pre a post vpre vpost st out Pr Po)).
 left. exists v, s1, [], out. split; [exact A|]. split; [exact F|symmetry; apply after_nil].
Qed.
Lemma evapp_prim : forall f vs st v, p f = None -> op f vs st = Out (Returned v) st [] ->
 evapp p op f vs st (Out (Returned v) st []).
Proof. intros f vs st v D E. apply evapp_op; [exact D|]. split; [apply returned_completed|exact E]. Qed.
End Steps.

(* Pure-expression evaluation, as in OrderCallPass (its tactics are local to
   that section), for the generator [counter]. *)
Definition P := Pass.P.
Definition op := Pass.op counter.
Ltac decisions := repeat match goal with Q : _ = true |- _ => rewrite Q | Q : _ = false |- _ => rewrite Q end.
Ltac sel := cbv beta iota zeta fix delta [L fold_right negb andb orb Pass.symbol_is]; decisions;
 cbn [String.eqb Ascii.eqb Bool.eqb]; cbv beta iota zeta fix delta [L fold_right negb andb orb Pass.symbol_is].
Ltac Y := match goal with
 | |- yields _ _ _ (Lit _) _ => apply yields_lit
 | |- yields _ _ _ (Var _) _ => apply yields_var; reflexivity
 | |- yields _ _ _ (If _ _ _) _ => eapply yields_if; [Y|sel; Y]
 | |- yields _ _ _ (And _ _) _ => eapply yields_and; [Y|sel; Y]
 | |- yields _ _ _ (Or _ _) _ => eapply yields_or; [Y|sel; Y]
 | |- yields _ _ _ (Let _ _ _) _ => eapply yields_let; [Y|Y]
 | |- yields _ _ _ (Call _ _) _ => eapply Pass.yields_call_returns; [Yargs|R]
 end
with R := first
 [ solve [match goal with H : Pass.returns _ _ _ _ |- _ => apply H | H : forall _, Pass.returns _ _ _ _ |- _ => apply H
          | H : forall _ _, Pass.returns _ _ _ _ |- _ => apply H end]
 | eapply Pass.returns_prim; [reflexivity|intro; reflexivity]
 | eapply Pass.returns_def; [reflexivity|reflexivity|cbn [Native.body Native.params]; Y] ]
with Yargs := match goal with
 | |- Forall2 _ [] _ => constructor
 | |- Forall2 _ (_::_) _ => econstructor; [Y|Yargs]
 end.
Ltac cond_goal := match goal with |- ev _ _ ?rho (If ?c _ _) _ _ =>
  let Cn := fresh "Cn" in eassert (Cn : yields P op rho c _) by Y;
  apply (proj2 (ev_if_yields _ _ _ _ _ _ _ _ _ Cn)); sel; clear Cn end.

(* ---------- the fresh loop terminates ---------- *)
Lemma gensym_ev : forall rho z, ev P op rho (Call "kl:gensym" [Lit (Symbol "arg")]) (Integer z)
 (Out (Returned (Symbol (gname (z + 1)))) (Integer (z + 1)) []).
Proof.
 intros rho z. apply (proj2 (ev_call_yields P op rho _ _ [Symbol "arg"] _ _ (Forall2_cons _ _ (yields_lit P op rho _) (Forall2_nil _)))).
 apply evapp_op; [reflexivity|]. split; [apply returned_completed|reflexivity].
Qed.
Lemma fresh_step : forall u z out,
 evapp P op "kl:_scm.fresh-call-variable" [u] (Integer z) out <->
 if Nat.eqb (O.occurrences (gname (z + 1)) u) 0
 then out = Out (Returned (Symbol (gname (z + 1)))) (Integer (z + 1)) []
 else evapp P op "kl:_scm.fresh-call-variable" [u] (Integer (z + 1)) out.
Proof.
 intros u z out. rewrite (evapp_def P op _ [u] _ _ out Pass.fresh_def eq_refl). cbn [Native.body Native.params].
 unfold Pass.fresh_body.
 assert (G := gensym_ev (arguments ["V5973"] [u]) z).
 assert (Gd := Pass.guard_symbol counter u (gname (z + 1))).
 split; intro H.
 - apply (ev_let_state_inv P op _ _ _ _ _ _ _ _ G) in H.
   apply (proj1 (ev_if_yields _ _ _ _ _ _ _ _ _ Gd)) in H.
   destruct (O.occurrences (gname (z + 1)) u) as [|k] eqn:Oc; cbn [Z.of_nat Z.eqb Nat.eqb] in H |- *.
   + exact (proj1 (ev_var P op _ "W5974" (Symbol (gname (z + 1))) _ _ eq_refl) H).
   + apply (proj1 (ev_call_yields P op _ _ _ [u] _ _
       (Forall2_cons _ _ (yields_var P op (Native.bind (arguments ["V5973"] [u]) "W5974" (Symbol (gname (z + 1)))) "V5973" u eq_refl) (Forall2_nil _)))) in H. exact H.
 - apply (ev_let_state P op _ _ _ _ _ _ _ _ G).
   apply (proj2 (ev_if_yields _ _ _ _ _ _ _ _ _ Gd)).
   destruct (O.occurrences (gname (z + 1)) u) as [|k] eqn:Oc; cbn [Z.of_nat Z.eqb Nat.eqb] in H |- *.
   + subst out. exact (proj2 (ev_var P op _ "W5974" (Symbol (gname (z + 1))) _ _ eq_refl) eq_refl).
   + apply (proj2 (ev_call_yields P op _ _ _ [u] _ _
       (Forall2_cons _ _ (yields_var P op (Native.bind (arguments ["V5973"] [u]) "W5974" (Symbol (gname (z + 1)))) "V5973" u eq_refl) (Forall2_nil _)))). exact H.
Qed.
(* The fresh loop returns, for every used syntax and every counter value. *)
Theorem fresh_progress : forall u z, exists j, (1 <= j <= Z.of_nat (S (List.length (syms u))))%Z /\
 O.occurrences (gname (z + j)) u = 0 /\
 evapp P op "kl:_scm.fresh-call-variable" [u] (Integer z) (Out (Returned (Symbol (gname (z + j)))) (Integer (z + j)) []).
Proof.
 intros u z. destruct (absent_candidate u z) as [d [Ld A]].
 (* the first absent candidate is reached; its index is at most d + 1 *)
 assert (Gen : forall e z', (z' - z <= Z.of_nat (S d) - Z.of_nat (S e))%Z -> (z <= z')%Z ->
   O.occurrences (gname (z' + Z.of_nat (S e))) u = 0 ->
   exists j, (1 <= j <= Z.of_nat (S e))%Z /\ O.occurrences (gname (z' + j)) u = 0 /\
   evapp P op "kl:_scm.fresh-call-variable" [u] (Integer z') (Out (Returned (Symbol (gname (z' + j)))) (Integer (z' + j)) [])).
 { induction e as [|e IH]; intros z' Bd Lo Ae.
   - exists 1%Z. replace (z' + Z.of_nat 1)%Z with (z' + 1)%Z in Ae by lia.
     split; [lia|split; [exact Ae|]]. apply fresh_step. rewrite Ae. reflexivity.
   - destruct (Nat.eqb (O.occurrences (gname (z' + 1)) u) 0) eqn:E.
     + exists 1%Z. apply Nat.eqb_eq in E. split; [lia|split; [exact E|]]. apply fresh_step. rewrite E. reflexivity.
     + replace (z' + Z.of_nat (S (S e)))%Z with ((z' + 1) + Z.of_nat (S e))%Z in Ae by lia.
       destruct (IH (z' + 1)%Z ltac:(lia) ltac:(lia) Ae) as [j [J [Oj F]]].
       exists (1 + j)%Z. replace (z' + (1 + j))%Z with (z' + 1 + j)%Z by lia.
       split; [lia|split; [exact Oj|]]. apply fresh_step. rewrite E. exact F. }
 destruct (Gen d z ltac:(lia) ltac:(lia) A) as [j [J R]]. exists j. split; [lia|exact R].
Qed.

(* ---------- the input loop terminates ---------- *)
Theorem inputs_progress : forall f, String.eqb "let*" f = false -> String.eqb "let" f = false ->
 forall xs r u z, Pass.bottom f r xs ->
 exists c z', evapp P op "kl:_scm.order-call-inputs" [L xs; L r; u] (Integer z) (Out (Returned c) (Integer z') []).
Proof.
 intros f Q1 Q2 xs. assert (RV := Pass.reverse_returns counter). assert (SR := Pass.simple_returns counter).
 assert (NR := Pass.not_returns counter). assert (HC := Pass.has_comp_returns counter).
 induction xs as [|x xs IH]; intros r u z Bot;
  match goal with |- exists _ _, evapp _ _ _ [?lx; _; _] _ _ =>
  (cut (exists c z', ev P op (arguments ["V5977"; "V5978"; "V5979"] [lx; L r; u]) Pass.inputs_body (Integer z)
     (Out (Returned c) (Integer z') []));
   [intros [c [z' H]]; exists c, z'; apply (proj2 (evapp_def P op _ [lx; L r; u] _ _ _ Pass.inputs_def eq_refl)); exact H|]) end;
  unfold Pass.inputs_body.
 - exists (L (rev r)), z. cond_goal.
   match goal with |- ev _ _ ?rho ?e _ _ => assert (Ye : yields P op rho e (L (rev r))) by Y end.
   apply Ye.
 - destruct (Pass.simple x) eqn:Sx; destruct (Pass.has_comp xs) eqn:Hx.
   1,2,4:
     (destruct (IH (x::r) u z) as [c [z' Hc]];
      [destruct Bot as [[r0 E]|[E [t T]]];
        [left; exists (x::r0); subst r; reflexivity|left; exists []; subst r; inversion T; reflexivity]|]);
     exists c, z'; cond_goal; cond_goal;
     match goal with |- ev _ _ ?rho (Let ?s ?a ?b) _ _ =>
       let Ya := fresh in eassert (Ya : yields P op rho a _) by Y;
       apply (proj2 (ev_let_yields _ _ _ _ _ _ _ _ _ Ya)) end;
     match goal with |- ev _ _ ?rho (Call _ ?es) _ _ =>
       let A := fresh in eassert (A : Forall2 (yields P op rho) es _) by Yargs;
       apply (proj2 (ev_call_yields _ _ _ _ _ _ _ _ A)) end;
     exact Hc.
   (* lift: x computes and a later argument computes *)
   destruct Bot as [[r0 E]|[E [t T]]]; [|inversion T; subst x; discriminate Sx].
   destruct (fresh_progress u z) as [j [_ [Occ F]]]. set (name := gname (z + j)).
   destruct (IH (Symbol name :: r) (Pair (Symbol name) u) (z + j)%Z) as [c' [z2 Hc]];
    [left; exists (Symbol name :: r0); subst r; reflexivity|].
   destruct (Pass.inputs_success counter f Q1 Q2 xs (Symbol name :: r) (Pair (Symbol name) u) _ c' _ _
     ltac:(left; exists (Symbol name :: r0); subst r; reflexivity) Hc) as [_ Sh].
   destruct (Pass.merge_shaped counter f (L [Symbol name; x]) c' Q1 Q2 Sh) as [MR _].
   exists (Pass.merge_spec (L [Symbol name; x]) c'), z2. cond_goal; cond_goal; cond_goal.
   apply (ev_let_state P op _ _ _ _ _ (Symbol name) (Integer (z + j))).
   { match goal with |- ev _ _ ?rho (Call _ ?es) _ _ =>
       let A := fresh in eassert (A : Forall2 (yields P op rho) es _) by Yargs;
       apply (proj2 (ev_call_yields _ _ _ _ _ _ _ _ A)) end. exact F. }
   apply (ev_focus_state P op _ _ [] _ [] [] [] (Integer (z + j)) (L [Symbol "let"; L [L [Symbol name; x]]; c']) (Integer z2));
    [constructor|constructor| |exact (MR (Integer z2))].
   apply (ev_focus_state P op _ _ [Lit (Symbol "let")] _ [] [Symbol "let"] [] (Integer (z + j))
     (L [L [L [Symbol name; x]]; c']) (Integer z2)); [Yargs|constructor| |apply evapp_prim; reflexivity].
   match goal with |- ev _ _ ?rho (Let ?s ?a ?b) _ _ =>
     let Ya := fresh in eassert (Ya : yields P op rho a _) by Y;
     apply (proj2 (ev_let_yields _ _ _ _ _ _ _ _ _ Ya)) end.
   apply (ev_focus_state P op _ _ [Var "_scm.arg5984"] _ [] [L [L [Symbol name; x]]] [] (Integer (z + j))
     c' (Integer z2)); [Yargs|constructor| |apply evapp_prim; reflexivity].
   do 2 (match goal with |- ev _ _ ?rho (Let ?s ?a ?b) _ _ =>
     let Ya := fresh in eassert (Ya : yields P op rho a _) by Y;
     apply (proj2 (ev_let_yields _ _ _ _ _ _ _ _ _ Ya)) end).
   match goal with |- ev _ _ ?rho (Call _ ?es) _ _ =>
     let A := fresh in eassert (A : Forall2 (yields P op rho) es _) by Yargs;
     apply (proj2 (ev_call_yields _ _ _ _ _ _ _ _ A)) end.
   exact Hc.
Qed.

(* The whole captured pass succeeds on every application call (head not a
   special-form keyword), from every counter value, without events. *)
Theorem order_call_progress : forall f args z, ~ In f D.keywords ->
 exists c z', evapp P op "kl:_scm.order-call" [L (Symbol f :: args)] (Integer z) (Out (Returned c) (Integer z') []).
Proof.
 intros f args z K. destruct (C.keyword_neq f K) as [Q1 Q2].
 destruct (inputs_progress f Q1 Q2 (Symbol f :: args) [] (L (Symbol f :: args)) z) as [c [z' H]];
  [right; split; [reflexivity|exists args; reflexivity]|].
 exists c, z'.
 assert (Df : P "kl:_scm.order-call" = Some (Def ["V5985"] (Call "kl:_scm.order-call-inputs" [Var "V5985"; Lit Nil; Var "V5985"]))) by reflexivity.
 apply (proj2 (evapp_def P op _ [L (Symbol f :: args)] _ _ _ Df eq_refl)). cbn [Native.body Native.params].
 match goal with |- ev _ _ ?rho (Call _ ?es) _ _ =>
   let A := fresh in eassert (A : Forall2 (yields P op rho) es _) by Yargs;
   apply (proj2 (ev_call_yields _ _ _ _ _ _ _ _ A)) end.
 exact H.
Qed.

(* ---------- unconditional composed preservation ---------- *)
Theorem order_call_preserves_total : forall N f args es z,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 exists c z', evapp P op "kl:_scm.order-call" [L (Symbol f :: args)] (Integer z) (Out (Returned c) (Integer z') []) /\
  exists target, decode (S (S N)) c = Some target /\
  forall p op' rho st out, Pre.bound_args rho es ->
   (ev p op' rho (Call f es) st out <-> ev p op' rho target st out).
Proof.
 intros N f args es z K Dc NL. destruct (order_call_progress f args z K) as [c [z' H]].
 exists c, z'. split; [exact H|]. exact (Pre.order_call_preserves counter N f args es _ c _ _ K Dc NL H).
Qed.

Theorem order_then_merge_total : forall cexp ordc ext ys1 ys2 N f args es x cv a z,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 decode (S N) cv = Some a ->
 exists c z' merged target,
  evapp P op "kl:_scm.order-call" [L (Symbol f :: args)] (Integer z) (Out (Returned c) (Integer z') []) /\
  B.returns cexp ordc ext ys1 ys2 "kl:_scm.merge-nested-lets" [C.naive_let x cv c] merged /\
  decode (S (S (S N))) (C.naive_let x cv (L (Symbol f :: args))) = Some (Let x a (Call f es)) /\
  decode (S (S N)) merged = Some target /\
  forall p op' rho st out, Pre.bound_args rho es ->
   (ev p op' rho (Let x a (Call f es)) st out <-> ev p op' rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 N f args es x cv a z K Dc NL Dv.
 destruct (order_call_progress f args z K) as [c [z' H]].
 destruct (C.order_then_merge_preserves cexp ordc ext ys1 ys2 counter N f args es x cv a _ c _ _ K Dc NL Dv H)
  as [merged [target R]].
 exists c, z', merged, target. split; [exact H|exact R].
Qed.

(* The let clause of compile-expression with the real counter. Premises
   about the uncaptured dispatcher: compiling the bound value returns `cv`
   (read as `a`) leaving an integer counter, and compiling the body (a static
   application) is the captured order-call. No run of emit-let, the pass or
   the merge is assumed: all three are proved to return. *)
Theorem let_clause_total : forall cexp ordc ext ys1 ys2 N f args es x v b s a st cv z e1,
 ~ In f D.keywords -> decode (S N) (L (Symbol f :: args)) = Some (Call f es) -> Forall Pre.no_lambda args ->
 cexp v s st = Out (Returned cv) (Integer z) e1 -> decode (S N) cv = Some a ->
 (forall st', evapp P op "kl:_scm.order-call" [L (Symbol f :: args)] st' (cexp b (Pair (Symbol x) s) st')) ->
 exists m z' r target,
  evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.emit-let" [Symbol x; v; b; s] st (Out (Returned m) (Integer z') e1) /\
  evapp B.P (B.op cexp ordc ext ys1 ys2) "kl:_scm.merge-nested-lets" [m] (Integer z') (Out (Returned r) (Integer z') []) /\
  decode (S (S N)) r = Some target /\
  forall p op' rho st out, Pre.bound_args rho es ->
   (ev p op' rho (Let x a (Call f es)) st out <-> ev p op' rho target st out).
Proof.
 intros cexp ordc ext ys1 ys2 N f args es x v b s a st cv z e1 K Dc NL CV Dv CB.
 destruct (order_then_merge_total cexp ordc ext ys1 ys2 N f args es x cv a z K Dc NL Dv)
  as [c [z' [merged [target [H [R [_ [DT EQ]]]]]]]].
 pose proof (evapp_det _ _ _ _ _ _ _ (CB (Integer z)) H) as Eb.
 exists (C.naive_let x cv c), z', merged, target. split; [|split; [exact (R (Integer z'))|split; [exact DT|exact EQ]]].
 apply (proj2 (B.emit_let_exact cexp ordc ext ys1 ys2 (Symbol x) v b s st _)).
 split; [apply returned_completed|].
 unfold B.emit_let_spec, bind, ret, return_result. rewrite CV. cbn [answer records trace]. rewrite Eb.
 cbn [answer records trace]. rewrite !app_nil_r. reflexivity.
Qed.
End OrderCallProgress.
