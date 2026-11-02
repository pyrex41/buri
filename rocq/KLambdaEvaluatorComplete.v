(* E2E-07 completeness (the converse of klambda_refines_ext). For every term
   of the extended KL-PURE-1 subset whose KLambda run terminates silently (no
   IO, KLMetatheory.run returns VDone [] o), the actual captured
   shen/klambda.shen evaluator, given a budget larger than the KLambda step
   count and enough Native fuel, returns [returned v] with o = Normal (tr_rv v)
   or [raised m] with o = Error x of the class of m.

   Proof structure: strong induction on the number of KLambda steps to
   termination. The evaluator answer is constructed with the forward
   equations of KLambdaEvaluatorEquations/Global/Forward; each sub-answer is
   placed on the KLambda path with the soundness theorem
   (KLambdaEvaluatorExtended, reaches2) and the remaining step count follows by
   determinism (halts_taus). The budget is never exhausted because every
   budget decrement of the evaluator corresponds to at least one KLambda step;
   [unsupported closure-equality] cannot occur because the machine would go
   wrong, which a terminating run excludes. *)
From Coq Require Import List String ZArith NArith Bool Lia Ascii.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory Native NativeComposition
 EqualityInductionOracle KLambdaEvaluatorCapture KLambdaEvaluatorEquations KLambdaEvaluatorPrimitives
 KLambdaEvaluatorRefinement KLambdaEvaluatorGlobal KLambdaEvaluatorExtended KLambdaEvaluatorForward.
Import ListNotations.
Module KLambdaEvaluatorComplete.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Module C := KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module Pr := KLambdaEvaluatorPrimitives.KLambdaEvaluatorPrimitives.
Module Q := KLambdaEvaluatorEquations.KLambdaEvaluatorEquations.
Module R := KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.
Module G := KLambdaEvaluatorGlobal.KLambdaEvaluatorGlobal.
Module X := KLambdaEvaluatorExtended.KLambdaEvaluatorExtended.
Module F := KLambdaEvaluatorForward.KLambdaEvaluatorForward.
Module NC := NativeComposition.NativeComposition.
Import C.
Open Scope string_scope.

(* ---------- the oracle answer is an actual Native.run answer ---------- *)
Lemma exec_if : forall p rho c a b x v, NC.executes p rho c x ->
 NC.executes p rho (match x with Native.Native.Boolean false => b | _ => a end) v ->
 NC.executes p rho (Native.Native.If c a b) v.
Proof.
 intros p rho c a b x v [n N] [m M]; exists (S (n + m)). cbn [Native.Native.eval].
 rewrite (NC.eval_monotone _ _ _ _ _ N (n + m)) by lia.
 destruct x as [| | | | | |[|]| | |]; eapply NC.eval_monotone; eauto; lia.
Qed.
Lemma exec_and : forall p rho a b x v, NC.executes p rho a x ->
 (match x with Native.Native.Boolean false => v = Native.Native.Boolean false | _ => NC.executes p rho b v end) ->
 NC.executes p rho (Native.Native.And a b) v.
Proof.
 intros p rho a b x v [n N] M.
 destruct x as [| | | | | |[|]| | |];
   try (destruct M as [m M]; exists (S (n + m)); cbn [Native.Native.eval];
        rewrite (NC.eval_monotone _ _ _ _ _ N (n + m)) by lia; eapply NC.eval_monotone; eauto; lia).
 subst v. exists (S n). cbn [Native.Native.eval]. rewrite N. reflexivity.
Qed.
Lemma exec_or : forall p rho a b x v, NC.executes p rho a x ->
 (match x with Native.Native.Boolean false => NC.executes p rho b v | _ => v = x end) ->
 NC.executes p rho (Native.Native.Or a b) v.
Proof.
 intros p rho a b x v [n N] M.
 destruct x as [| | | | | |[|]| | |];
   try (subst v; exists (S n); cbn [Native.Native.eval]; rewrite N; reflexivity).
 destruct M as [m M]; exists (S (n + m)); cbn [Native.Native.eval].
 rewrite (NC.eval_monotone _ _ _ _ _ N (n + m)) by lia. eapply NC.eval_monotone; eauto; lia.
Qed.
Lemma step_exec : forall k e rho v, O.step defined (ask k) rho e = Some v ->
 NC.executes (Native.Native.lookup program) rho e v.
Proof.
 induction k as [k IHk] using (well_founded_induction lt_wf).
 intro e; induction e as [w0|x0|c a b IHc IHa IHb|x0 a b IHa IHb|a b IHa IHb|a b IHa IHb|s0 es IHes]
   using O.expr_rect'; intros rho w HS; cbn [O.step] in HS.
 - injection HS as <-. apply NC.literal.
 - apply NC.variable; exact HS.
 - destruct (O.step defined (ask k) rho c) as [x|] eqn:E1; [|discriminate].
   apply (exec_if _ _ _ _ _ x); [apply IHc; exact E1|].
   destruct x as [| | | | | |[|]| | |]; auto.
 - destruct (O.step defined (ask k) rho a) as [x|] eqn:E1; [|discriminate].
   apply (NC.binding _ _ _ _ _ x); [apply IHa; exact E1|apply IHb; exact HS].
 - destruct (O.step defined (ask k) rho a) as [x|] eqn:E1; [|discriminate].
   apply (exec_and _ _ _ _ x); [apply IHa; exact E1|].
   destruct x as [| | | | | |[|]| | |]; auto; congruence.
 - destruct (O.step defined (ask k) rho a) as [x|] eqn:E1; [|discriminate].
   apply (exec_or _ _ _ _ x); [apply IHa; exact E1|].
   destruct x as [| | | | | |[|]| | |]; auto; congruence.
 - match type of HS with match ?m with _ => _ end = _ => destruct m as [vs|] eqn:M; [|discriminate] end.
   assert (A : forall xs ws, (forall e, In e xs -> In e es) ->
     (fix many es := match es with
     | [] => Some []
     | e::es => match O.step defined (ask k) rho e,many es with Some v,Some vs => Some (v::vs) | _,_ => None end end) xs = Some ws ->
     Forall2 (NC.executes (Native.Native.lookup program) rho) xs ws).
   { induction xs as [|a xs IHx]; intros ws Sb W; [injection W as <-; constructor|].
     destruct (O.step defined (ask k) rho a) eqn:Ea; [|discriminate].
     match type of W with match ?m with _ => _ end = _ => destruct m eqn:Rm; [|discriminate] end.
     injection W as <-. constructor; [apply (IHes a (Sb a (or_introl eq_refl))); exact Ea|].
     apply IHx; [intros e' I; apply Sb; right; exact I|first [exact Rm|reflexivity]]. }
   pose proof (A es vs (fun e I => I) M) as Fa. clear A M.
   rewrite defined_lookup in HS. destruct (Native.Native.lookup program s0) as [d|] eqn:D.
   + destruct k as [|k]; [discriminate|]. rewrite (ask_unfold _ _ _ _ D) in HS.
     destruct (Nat.eqb (List.length (Native.Native.params d)) (List.length vs)) eqn:Lq; [|discriminate].
     apply (NC.call _ _ _ _ vs); [exact Fa|]. exists d; split; [exact D|split; [apply Nat.eqb_eq; exact Lq|]].
     exact (IHk k (le_n _) _ _ _ HS).
   + destruct (Native.Native.external s0 vs) eqn:Ex; try discriminate. injection HS as <-.
     exact (NC.primitive_call _ _ _ _ _ _ Fa D Ex).
Qed.
Lemma ask_run : forall k name args r, ask k name args = Some r ->
 exists n0, forall n, n0 <= n -> Native.Native.run n program name args = Native.Native.Returned r.
Proof.
 intros [|k] name args r H; [discriminate|].
 destruct (Native.Native.lookup program name) as [d|] eqn:D; [|unfold ask, O.oracle in H; cbv beta iota fix in H; rewrite D in H; discriminate].
 rewrite (ask_unfold _ _ _ _ D) in H.
 destruct (Nat.eqb (List.length (Native.Native.params d)) (List.length args)) eqn:Lq; [|discriminate].
 destruct (step_exec k _ _ _ H) as [n0 N]. exists n0. intros n L.
 unfold Native.Native.run. rewrite D, Lq. exact (NC.eval_monotone _ _ _ _ _ N n L).
Qed.

(* ---------- counted silent runs ---------- *)
Inductive tausn (P : profile) : nat -> config -> config -> Prop :=
 | tn0 c : tausn P 0 c c
 | tnS n c c' c'' : next P c = MTau c' -> tausn P n c' c'' -> tausn P (S n) c c''.
Definition halts (P : profile) (c : config) (n : nat) : Prop :=
 exists c' o, tausn P n c c' /\ next P c' = MFinal o.
Lemma halts_next : forall P c n, halts P c n ->
 (n = 0 /\ exists o, next P c = MFinal o) \/ (exists n' c', n = S n' /\ next P c = MTau c' /\ halts P c' n').
Proof.
 intros P c n (c' & o & T & Fn). inversion T as [c0|n' c0 c1 c2 N T']; subst.
 - left; eauto.
 - right; exists n', c1; split; [reflexivity|split; [exact N|exists c', o; split; assumption]].
Qed.
Lemma halts_step : forall P c c' n, next P c = MTau c' -> halts P c n -> exists n', n = S n' /\ halts P c' n'.
Proof.
 intros P c c' n N H. destruct (halts_next P c n H) as [[_ (o & Fo)]|(n' & c1 & -> & N1 & H1)].
 - rewrite N in Fo; discriminate.
 - rewrite N in N1; injection N1 as <-. eauto.
Qed.
Lemma halts_tausn : forall P j c c' n, tausn P j c c' -> halts P c n -> j <= n /\ halts P c' (n - j).
Proof.
 intros P j c c' n T; revert n; induction T as [c|j c c1 c2 N T IH]; intros n H.
 - split; [lia|]. replace (n - 0) with n by lia. exact H.
 - destruct (halts_step P c c1 n N H) as (n' & -> & H1). destruct (IH n' H1) as [L H2].
   split; [lia|]. replace (S n' - S j) with (n' - j) by lia. exact H2.
Qed.
Lemma taus_tausn : forall P c c', R.taus P c c' -> exists j, tausn P j c c'.
Proof.
 intros P c c' T; induction T as [c|c c1 c2 N T [j IH]]; [exists 0; constructor|exists (S j); econstructor; eauto].
Qed.
Lemma halts_taus : forall P c c' n, halts P c n -> R.taus P c c' -> exists j, j <= n /\ halts P c' j.
Proof.
 intros P c c' n H T. destruct (taus_tausn P c c' T) as [j Tj].
 destruct (halts_tausn P j c c' n Tj H) as [L H']. exists (n - j); split; [lia|exact H'].
Qed.
Lemma halts_wrong : forall P c n w k s, halts P c n -> R.taus P c (Cfg (Wrong w) k s) -> False.
Proof.
 intros P c n w k s H T. destruct (halts_taus P _ _ n H T) as (j & _ & Hj).
 destruct (halts_next P _ j Hj) as [[_ (o & Fo)]|(n' & c1 & _ & N1 & _)]; cbn in *; discriminate.
Qed.
(* A silent terminating KLambda.run is a counted silent path to a final state. *)
Lemma krun_halts : forall P m c o, R.krun P m c tt = VDone [] o -> exists n, n <= m /\ halts P c n.
Proof.
 intros P m; induction m as [|m IH]; intros c o E; unfold R.krun in E; cbn [KLMetatheory.KLMetatheory.run] in E.
 - destruct (next P c) eqn:N; try discriminate. exists 0; split; [lia|exists c, o0; split; [constructor|exact N]].
 - destruct (next P c) as [c1|q kk|o1|w] eqn:N; try discriminate.
   + unfold KLMetatheory.KLMetatheory.cnext in E. rewrite N in E. cbn -[KLMetatheory.KLMetatheory.run] in E.
     change (R.still tt) with tt in E.
     destruct (KLMetatheory.KLMetatheory.run unit R.env_none R.quiet R.still P m c1 tt) eqn:Rm; cbn in E; try discriminate.
     injection E as -> ->. destruct (IH c1 o Rm) as (n & L & c' & o' & T & Fo).
     exists (S n); split; [lia|]. exists c', o'; split; [econstructor; eauto|exact Fo].
   + unfold KLMetatheory.KLMetatheory.cnext in E. rewrite N in E. cbn -[KLMetatheory.KLMetatheory.run] in E.
     destruct (KLMetatheory.KLMetatheory.run _ _ _ _ _ _ _ _); cbn in E; discriminate.
   + exists 0; split; [lia|exists c, o1; split; [constructor|exact N]].
Qed.

Definition decided (w : verdict) : Prop := match w with WRet _ | WRaise _ => True | _ => False end.
Lemma gate_ok : forall z r, (0 < z)%Z -> gate z r = r.
Proof. intros z r L. unfold gate. destruct z; [lia|reflexivity|lia]. Qed.
Lemma prim_spec_nb : forall op vs, Pr.prim_spec op vs <> WBudget.
Proof.
 intros op vs E. unfold Pr.prim_spec in E.
 repeat match type of E with context [match ?o with _ => _ end] => destruct o end; discriminate.
Qed.

Section Main.
Variables (ds : list G.defn) (P : profile) (s : store).
Hypotheses (Hds : X.ds_ok ds) (HP : X.pure2 P) (Hs : R.prims s) (Hd : X.defs s ds).
Let D := G.enc_defs ds.
Lemma Hst : stack_limit P = None. Proof. exact (proj1 (proj1 HP)). Qed.
Ltac nx := cbn -[of_string kw lookup R.tr_env kl_eq]; unfold push, continue_with; rewrite ?Hst; cbn -[of_string kw lookup R.tr_env kl_eq].
Ltac hstep H := match type of H with halts P ?c ?n =>
 let N := fresh "N" in eassert (N : next P c = MTau _) by (nx; reflexivity);
 let n' := fresh "n" in let H' := fresh "H" in
 destruct (halts_step P _ _ n N H) as (n' & -> & H'); clear H N; rename H' into H end.
Ltac hstep2 H := match type of H with halts P ?c ?n =>
 let N := fresh "N" in eassert (N : next P c = MTau _) by (nx; first [
   (cbn [lookup]; rewrite ?R.text_eqb_of_string; cbn -[R.tr_env of_string kl_eq]; reflexivity) |
   rewrite (R.call_prim P s (proj1 HP) Hs "error-to-string" PErrorToString) by (cbn; first [tauto|reflexivity]); reflexivity |
   reflexivity]);
 let n' := fresh "n" in let H' := fresh "H" in
 destruct (halts_step P _ _ n N H) as (n' & -> & H'); clear H N; rename H' into H end.
Ltac fuel K := destruct K as [|K]; [lia|].

Definition CE n := forall e env k z, X.sub2 e -> X.okenv2 ds env -> (Z.of_nat n < z)%Z ->
 halts P (Cfg (Eval (R.tr_env env) (R.tr e)) k s) n ->
 exists w F0, (forall K, F0 <= K -> ask K "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] =
   Some (enc_verdict w)) /\ decided w /\ X.okv ds w /\ X.ev P s e env w.
Definition CA n := forall fv av k z c, X.ok2 ds fv -> X.ok2 ds av -> (Z.of_nat n + 1 < z)%Z ->
 apply_value P (R.tr_rv fv) [R.tr_rv av] k s = MTau c -> halts P c n ->
 exists w F0, (forall K, F0 <= K -> ask K "kl:buri.apply-value" [D; enc fv; enc av; Native.Native.Integer z] =
   Some (enc_verdict w)) /\ decided w.
Definition CG n := forall es env k z g done e1 es', es = e1 :: es' -> Forall X.sub2 es -> X.okenv2 ds env ->
 (Z.of_nat n < z)%Z ->
 halts P (Cfg (Eval (R.tr_env env) (R.tr e1)) (KCallArgs g done (map R.tr es') (R.tr_env env) :: k) s) n ->
 exists a F0, (forall K, F0 <= K -> ask K "kl:buri.eval-args"
   [D; Native.Native.L (map enc_term es); enc_env env; Native.Native.Integer z] = Some (enc_args a)) /\
   match a with AVals vs => Forall (X.ok2 ds) vs /\ List.length vs = List.length es | AFail w => decided w end.

(* The evaluator's answer, once constructed, carries the soundness facts; an
   answer that is not exhaustion is decided, because [unsupported] would put
   the machine on a wrong state, which a terminating run excludes. *)
Lemma wrap_eval : forall e env k z n F0 w0, X.sub2 e -> X.okenv2 ds env -> w0 <> WBudget ->
 halts P (Cfg (Eval (R.tr_env env) (R.tr e)) k s) n ->
 (forall K, F0 <= K -> ask K "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] = Some (enc_verdict w0)) ->
 exists w F1, (forall K, F1 <= K -> ask K "kl:buri.eval" [D; enc_term e; enc_env env; Native.Native.Integer z] =
   Some (enc_verdict w)) /\ decided w /\ X.okv ds w /\ X.ev P s e env w.
Proof.
 intros e env k z n F0 w0 Se Oe NB H EF. destruct (X.all_fuel ds Hds F0 F0 (le_n _)) as [SE _].
 destruct (SE e env z _ Se Oe (EF F0 (le_n _))) as (w & Ew & Ow & Gw).
 assert (Ev : X.ev P s e env w) by (apply Gw; assumption).
 exists w, F0. split; [intros K L; rewrite (EF K L), Ew; reflexivity|]. split; [|split; assumption].
 destruct w as [v|m| |]; cbn; auto.
 - destruct w0; cbn in Ew; try discriminate Ew. contradiction.
 - destruct (Ev k) as (k' & s' & T). exact (halts_wrong P _ n _ _ _ H T).
Qed.

Lemma main : forall n, (forall m, m < n -> CE m /\ CA m /\ CG m) -> CE n /\ CA n /\ CG n.
Proof.
 intros n IH. assert (IE : forall m, m < n -> CE m) by (intros m L; apply (IH m L)).
 assert (IA : forall m, m < n -> CA m) by (intros m L; apply (IH m L)).
 assert (IG : forall m, m < n -> CG m) by (intros m L; apply (IH m L)).
 assert (CEn : CE n).
 { intros e env k z Se Oe Lz H. pose proof H as H0.
   destruct e as [d|x|x|x b|f a|x a b|c a b|op args|e|e h|e|e]; pose proof Se as Se0; cbn [X.sub2] in Se.
   - (* literal *)
     apply (wrap_eval _ _ k z n 1 (WRet d)); auto; [discriminate|].
     intros K LK. fuel K. rewrite Q.eval_lit, gate_ok by lia. reflexivity.
   - (* variable *)
     apply (wrap_eval _ _ k z n (List.length env + 3)
       (match assoc x env with Some v => WRet v | None => WRaise "unbound-variable" end)); auto;
       [destruct (assoc x env); discriminate|].
     intros K LK. fuel K. rewrite Q.eval_var, gate_ok by lia. fuel K.
     rewrite F.fwd_get by lia. destruct (assoc x env) as [v|]; [apply Q.lookup_found|apply Q.lookup_missing].
   - (* [global X] *)
     apply (wrap_eval _ _ k z n (List.length ds + 3)
       (match G.find_def x ds with None => WRaise "unbound-function" | Some _ => WRet (RFunction x []) end)); auto;
       [destruct (G.find_def x ds); discriminate|].
     intros K LK. fuel K. rewrite (F.fwd_eval_global K _ env z x (G.find_def x ds)).
     + unfold G.gate_value. rewrite (proj2 (Z.eqb_neq z 0)) by lia. destruct (G.find_def x ds); reflexivity.
     + fuel K. apply F.fwd_definition. lia.
   - (* lambda *)
     apply (wrap_eval _ _ k z n 1 (WRet (RClosure x b env))); auto; [discriminate|].
     intros K LK. fuel K. rewrite Q.eval_lambda, gate_ok by lia. reflexivity.
   - (* application *)
     destruct Se as [Sf Sa]. cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) f env (KHead [R.tr a] (R.tr_env env) :: k) (z - 1)%Z Sf Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [fv|m| |]; try contradiction.
     + pose proof (G1 (KHead [R.tr a] (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
       destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
       match type of H1 with halts _ _ ?m1 =>
       pose proof (IE m1 ltac:(lia) a env (KArgs (R.tr_rv fv) [] [] (R.tr_env env) :: k) (z - 1)%Z Sa Oe ltac:(lia) H1)
         as (w2 & F2 & E2 & D2 & O2 & G2) end.
       destruct w2 as [av|m| |]; try contradiction.
       * pose proof (G2 (KArgs (R.tr_rv fv) [] [] (R.tr_env env) :: k)) as T2. cbn [X.reaches2] in T2.
         destruct (halts_taus _ _ _ _ H1 T2) as (j2 & L2 & H2).
         destruct (halts_next _ _ _ H2) as [[_ (o & Fo)]|(j3 & c3 & -> & N3 & H3)].
         { cbn [next ctl kont mem ret_move rev List.app] in Fo.
           pose proof (KLMetatheory.KLMetatheory.apply_value_running P (R.tr_rv fv) [R.tr_rv av] k s) as Rn.
           rewrite Fo in Rn. contradiction. }
         cbn [next ctl kont mem ret_move rev List.app] in N3.
         destruct (IA j3 ltac:(lia) fv av k (z - 1)%Z c3 O1 O2 ltac:(lia) N3 H3) as (w3 & F3 & E3 & D3).
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + F3 + 3) w3); auto; [destruct w3; cbn in D3; try contradiction; discriminate|].
         intros K LK. fuel K. rewrite Q.eval_apply, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite Q.function_verdict, (E2 K) by lia. fuel K. rewrite Q.argument_verdict. apply E3. lia.
       * apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 3) (WRaise m)); auto; [discriminate|].
         intros K LK. fuel K. rewrite Q.eval_apply, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite Q.function_verdict, (E2 K) by lia. fuel K. rewrite Q.argument_verdict. reflexivity.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise m)); auto; [discriminate|].
       intros K LK. fuel K. rewrite Q.eval_apply, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.function_verdict. reflexivity.
   - (* let *)
     destruct Se as [Sa Sb]. cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) a env (KLet (of_string x) (R.tr b) (R.tr_env env) :: k) (z - 1)%Z Sa Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [v|m| |]; try contradiction.
     + pose proof (G1 (KLet (of_string x) (R.tr b) (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
       destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
       assert (O' : X.okenv2 ds ((x, v) :: env)) by (constructor; assumption).
       match type of H1 with halts _ _ ?m1 =>
       pose proof (IE m1 ltac:(lia) b ((x, v) :: env) k (z - 1)%Z Sb O' ltac:(lia) H1)
         as (w2 & F2 & E2 & D2 & O2 & G2) end.
       apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 3) w2); auto; [destruct w2; cbn in D2; try contradiction; discriminate|].
       intros K LK. fuel K. rewrite Q.eval_let, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.let_verdict. apply E2. lia.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise m)); auto; [discriminate|].
       intros K LK. fuel K. rewrite Q.eval_let, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.let_verdict. reflexivity.
   - (* if *)
     destruct Se as (Sc & Sa & Sb). cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) c env (KIf (R.tr a) (R.tr b) (R.tr_env env) :: k) (z - 1)%Z Sc Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [v|m| |]; try contradiction.
     + destruct v as [z0| [|] |st|sy| |a1 a2|x0 e0 env0|f0 g0|e0 env0];
       try (apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 4) (WRaise "nonboolean-condition")); auto; [discriminate|];
            intros K LK; fuel K; rewrite Q.eval_if, gate_ok by lia; rewrite (E1 K) by lia; fuel K; fuel K;
            rewrite F.fwd_if; reflexivity).
       * pose proof (G1 (KIf (R.tr a) (R.tr b) (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
         destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
         match type of H1 with halts _ _ ?m1 =>
         pose proof (IE m1 ltac:(lia) a env k (z - 1)%Z Sa Oe ltac:(lia) H1) as (w2 & F2 & E2 & D2 & O2 & G2) end.
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 4) w2); auto; [destruct w2; cbn in D2; try contradiction; discriminate|].
         intros K LK. fuel K. rewrite Q.eval_if, gate_ok by lia. rewrite (E1 K) by lia. fuel K. fuel K.
         rewrite F.fwd_if. apply E2. lia.
       * pose proof (G1 (KIf (R.tr a) (R.tr b) (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
         destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
         match type of H1 with halts _ _ ?m1 =>
         pose proof (IE m1 ltac:(lia) b env k (z - 1)%Z Sb Oe ltac:(lia) H1) as (w2 & F2 & E2 & D2 & O2 & G2) end.
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 4) w2); auto; [destruct w2; cbn in D2; try contradiction; discriminate|].
         intros K LK. fuel K. rewrite Q.eval_if, gate_ok by lia. rewrite (E1 K) by lia. fuel K. fuel K.
         rewrite F.fwd_if. apply E2. lia.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 4) (WRaise m)); auto; [discriminate|].
       intros K LK. fuel K. rewrite Q.eval_if, gate_ok by lia. rewrite (E1 K) by lia. fuel K. fuel K.
       rewrite F.fwd_if. reflexivity.
   - (* saturated primitive *)
     destruct Se as [Ar Sargs0]. apply X.sub2_fold in Sargs0. unfold R.prim_ok in Ar.
     destruct (R.prim_of op) as [p|] eqn:Op; [|contradiction].
     destruct args as [|e1 es']; [destruct p; discriminate Ar|].
     cbn [R.tr map] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IG m0 ltac:(lia) (e1 :: es') env k (z - 1)%Z (of_string op) [] e1 es' eq_refl Sargs0 Oe ltac:(lia) H) as (av & Fa & Ea & Da) end.
     destruct av as [vs|w1].
     + destruct Da as [Ovs Lvs]. rewrite <- Ar in Lvs.
       destruct (R.prim_cases op p Op) as [[I2 A2]|[[I1 A1]|[-> ->]]].
       * destruct vs as [|v1 [|v2 [|]]]; cbn in Lvs; try (rewrite A2 in Lvs; discriminate Lvs).
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (Fa + 3) (Pr.prim_spec op [v1; v2])); auto; [apply prim_spec_nb|].
         intros K LK. fuel K. rewrite Q.eval_prim, gate_ok by lia. rewrite (Ea K) by lia. fuel K.
         rewrite Q.primitive_args. fuel K. apply F.fwd_prim2; exact I2.
       * destruct vs as [|v1 [|]]; cbn in Lvs; try (rewrite A1 in Lvs; discriminate Lvs).
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (Fa + 3) (Pr.prim_spec op [v1])); auto; [apply prim_spec_nb|].
         intros K LK. fuel K. rewrite Q.eval_prim, gate_ok by lia. rewrite (Ea K) by lia. fuel K.
         rewrite Q.primitive_args. fuel K. apply F.fwd_prim1; exact I1.
       * destruct vs as [|v1 [|v2 [|]]]; cbn in Lvs; try discriminate Lvs.
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (Fa + F.eq_bound v1 + 5) (Pr.eq_spec v1 v2)); auto;
           [unfold Pr.eq_spec; destruct (Pr.eqv v1 v2); discriminate|].
         intros K LK. fuel K. rewrite Q.eval_prim, gate_ok by lia. rewrite (Ea K) by lia. fuel K.
         rewrite Q.primitive_args. fuel K. apply F.fwd_prim_equal. lia.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (Fa + 3) w1); auto; [destruct w1; cbn in Da; try contradiction; discriminate|].
       intros K LK. fuel K. rewrite Q.eval_prim, gate_ok by lia. rewrite (Ea K) by lia. fuel K.
       rewrite Q.primitive_args. reflexivity.
   - (* raise *)
     cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) e env (KCallArgs (of_string "simple-error") [] [] (R.tr_env env) :: k) (z - 1)%Z
       Se Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [v|m| |]; try contradiction.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3)
         (match v with RStr t => WRaise t | _ => WRaise "error-message-not-string" end)); auto;
         [destruct v; discriminate|].
       intros K LK. fuel K. rewrite Q.eval_raise, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.raise_verdict. destruct v; reflexivity.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise m)); auto; [discriminate|].
       intros K LK. fuel K. rewrite Q.eval_raise, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.raise_verdict. reflexivity.
   - (* trap *)
     destruct Se as [Se Sh]. cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) e env (KTrap (R.handler (R.tr h)) (R.tr_env env) :: k) (z - 1)%Z Se Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [v|m| |]; try contradiction.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRet v)); auto; [discriminate|].
       intros K LK. fuel K. rewrite Q.eval_trap, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite Q.trap_verdict. reflexivity.
     + destruct (G1 (KTrap (R.handler (R.tr h)) (R.tr_env env) :: k)) as (x & Cx & T1).
       destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). unfold R.handler in H1.
       hstep H1. hstep H1. hstep H1. hstep H1.
       match type of H1 with halts _ (Cfg _ ?k2 _) ?m1 =>
       pose proof (IE m1 ltac:(lia) h env k2 (z - 1)%Z Sh Oe ltac:(lia) H1) as (w2 & F2 & E2 & D2 & O2 & G2) end.
       destruct w2 as [hv|m2| |]; try contradiction.
       * match type of H1 with halts _ (Cfg _ ?k2 _) _ => pose proof (G2 k2) as T2 end. cbn [X.reaches2] in T2.
         destruct (halts_taus _ _ _ _ H1 T2) as (j2 & L2 & H2).
         pose proof (X.class_text2 P m x HP Cx) as Tx.
         assert (Hq : forall c3 j3, apply_value P (R.tr_rv hv) [R.tr_rv (RStr m)] k s = MTau c3 -> halts P c3 j3 ->
           j3 < j2 -> exists w3 F3, (forall K, F3 <= K -> ask K "kl:buri.apply-value"
             [D; enc hv; enc (RStr m); Native.Native.Integer (z - 1)%Z] = Some (enc_verdict w3)) /\ decided w3).
         { intros c3 j3 N3 H3 L3. exact (IA j3 ltac:(lia) hv (RStr m) k (z - 1)%Z c3 O2 I ltac:(lia) N3 H3). }
         assert (Hw : exists c3 j3, apply_value P (R.tr_rv hv) [R.tr_rv (RStr m)] k s = MTau c3 /\ halts P c3 j3 /\ j3 < j2).
         { clear Hq. destruct x; cbn in Tx;
           hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2; hstep2 H2;
           match type of H2 with halts _ ?c2 _ =>
             destruct (halts_next _ _ _ H2) as [[_ (o & Fo)]|(j3 & c3 & -> & N3 & H3)];
             [cbn [pout_config continue_with next ctl kont mem ret_move rev List.app] in Fo;
              pose proof (KLMetatheory.KLMetatheory.apply_value_running P (R.tr_rv hv) [R.tr_rv (RStr m)] k s) as Rn;
              cbn [R.tr_rv] in Rn; rewrite <- Tx in Rn; rewrite Fo in Rn; contradiction
             |exists c3, j3; split; [cbn [pout_config continue_with next ctl kont mem ret_move rev List.app] in N3; cbn [R.tr_rv]; rewrite <- Tx; exact N3|split; [exact H3|lia]]] end. }
         destruct Hw as (c3 & j3 & N3 & H3 & L3). destruct (Hq c3 j3 N3 H3 L3) as (w3 & F3 & E3 & D3).
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + F3 + 3) w3); auto; [destruct w3; cbn in D3; try contradiction; discriminate|].
         intros K LK. fuel K. rewrite Q.eval_trap, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite Q.trap_verdict, (E2 K) by lia. fuel K. rewrite Q.handler_verdict. apply E3. lia.
       * apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 3) (WRaise m2)); auto; [discriminate|].
         intros K LK. fuel K. rewrite Q.eval_trap, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite Q.trap_verdict, (E2 K) by lia. fuel K. rewrite Q.handler_verdict. reflexivity.
   - (* freeze *)
     apply (wrap_eval _ _ k z n 1 (WRet (RThunk e env))); auto; [discriminate|].
     intros K LK. fuel K. rewrite G.eval_freeze, gate_ok by lia. reflexivity.
   - (* thaw *)
     cbn [R.tr] in H. hstep H.
     match type of H with halts _ _ ?m0 => pose proof (IE m0 ltac:(lia) e env (KHead [] (R.tr_env env) :: k) (z - 1)%Z Se Oe ltac:(lia) H) as (w1 & F1 & E1 & D1 & O1 & G1) end.
     destruct w1 as [v|m| |]; try contradiction.
     + destruct v as [z0|b0|st|sy| |a1 a2|x0 e0 env0|f0 prev|e0 env0];
       try (apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise "not-callable")); auto; [discriminate|];
            intros K LK; fuel K; rewrite G.eval_thaw, gate_ok by lia; rewrite (E1 K) by lia; fuel K;
            rewrite G.thaw_verdict; reflexivity).
       * apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise "arity")); auto; [discriminate|].
         intros K LK. fuel K. rewrite G.eval_thaw, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite G.thaw_verdict. reflexivity.
       * destruct O1 as [(ps & b & Fd & Lt) Oargs].
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + List.length ds + List.length prev + 5) (WRet (RFunction f0 prev))); auto;
           [discriminate|].
         intros K LK. fuel K. rewrite G.eval_thaw, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite G.thaw_verdict. destruct K as [|K]; [lia|].
         unfold D; rewrite (F.fwd_definition ds f0 K) by lia. rewrite Fd.
         rewrite (F.fwd_apply_global K) by lia. apply Nat.ltb_lt in Lt. rewrite Lt. reflexivity.
       * destruct O1 as [Sb0 Oe0]. apply X.okenv2_fold in Oe0.
         pose proof (G1 (KHead [] (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
         destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
         match type of H1 with halts _ _ ?m1 =>
         pose proof (IE m1 ltac:(lia) e0 env0 k (z - 1)%Z Sb0 Oe0 ltac:(lia) H1) as (w2 & F2 & E2 & D2 & O2 & G2) end.
         apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + F2 + 3) w2); auto; [destruct w2; cbn in D2; try contradiction; discriminate|].
         intros K LK. fuel K. rewrite G.eval_thaw, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
         rewrite G.thaw_verdict. apply E2. lia.
     + apply (wrap_eval _ _ k z ltac:(match type of H0 with halts _ _ ?nn => exact nn end) (F1 + 3) (WRaise m)); auto; [discriminate|].
       intros K LK. fuel K. rewrite G.eval_thaw, gate_ok by lia. rewrite (E1 K) by lia. fuel K.
       rewrite G.thaw_verdict. reflexivity. }
 split; [exact CEn|split].
 - (* buri.apply-value *)
   intros fv av k z c Of Oa Lz N Hc.
   destruct fv as [z0|b0|st|sy| |a1 a2|x e env|g prev|e env].
   7: { cbn in N. injection N as <-. destruct Of as [Se Oe]. apply X.okenv2_fold in Oe.
        assert (O' : X.okenv2 ds ((x, av) :: env)) by (constructor; assumption).
        destruct (CEn e ((x, av) :: env) k (z - 1)%Z Se O' ltac:(lia) Hc) as (w & F0 & E & Dw & _ & _).
        exists w, (F0 + 2). split; [|exact Dw]. intros K LK. fuel K.
        rewrite Q.apply_value_eq by (intros; discriminate). rewrite gate_ok by lia. apply E. lia. }
   8: { exists (WRaise "arity"), 1. split; [|exact I]. intros K LK. fuel K.
        rewrite G.apply_value_thunk, gate_ok by lia. reflexivity. }
   7: { destruct Of as [(ps & b & Fd & Lt) Oargs]. apply X.oklist_fold in Oargs.
        assert (Oall : Forall (X.ok2 ds) (prev ++ [av])) by (apply Forall_app; split; [exact Oargs|constructor; [exact Oa|constructor]]).
        cbn [R.tr_rv apply_value] in N.
        replace (map R.tr_rv prev ++ [R.tr_rv av])%list with (map R.tr_rv (prev ++ [av])) in N by (rewrite map_app; reflexivity).
        rewrite (X.call_user P s ds HP Hs Hd g ps b (prev ++ [av]) k Fd) in N.
        destruct (Nat.ltb (List.length (prev ++ [av])) (List.length ps)) eqn:Lt2.
        - exists (WRet (RFunction g (prev ++ [av]))), (List.length ds + List.length prev + 6). split; [|exact I].
          intros K LK. fuel K. rewrite G.apply_value_function, gate_ok by lia. fuel K.
          unfold D; rewrite (F.fwd_definition ds g K) by lia. rewrite Fd.
          change (Native.Native.L [enc av]) with (Native.Native.L (map enc [av])). rewrite (F.fwd_append prev [av] K) by lia.
          rewrite (F.fwd_apply_global K) by (rewrite app_length; cbn; lia). rewrite Lt2. reflexivity.
        - injection N as <-. apply Nat.ltb_ge in Lt2. rewrite app_length in Lt2. cbn in Lt2.
          assert (Eq : List.length (prev ++ [av]) = List.length ps) by (rewrite app_length; cbn; lia).
          rewrite <- Eq in Hc.
          rewrite <- (map_length R.tr_rv (prev ++ [av])) in Hc. rewrite skipn_all, firstn_all in Hc.
          cbn [continue_with] in Hc. rewrite <- X.tr_env_combine in Hc.
          destruct (X.find_def_ok ds g ps b Hds Fd) as [_ Sb].
          destruct (CEn b (combine ps (prev ++ [av])) k (z - 1)%Z Sb (X.combine_ok2 ds ps _ Oall) ltac:(lia) Hc)
            as (w & F0 & E & Dw & _ & _).
          exists w, (F0 + List.length ds + List.length prev + List.length ps + 8). split; [|exact Dw].
          intros K LK. fuel K. rewrite G.apply_value_function, gate_ok by lia. fuel K.
          unfold D; rewrite (F.fwd_definition ds g K) by lia. rewrite Fd.
          change (Native.Native.L [enc av]) with (Native.Native.L (map enc [av])). rewrite (F.fwd_append prev [av] K) by lia.
          rewrite (F.fwd_apply_global K) by (rewrite app_length; cbn; lia).
          replace (Nat.ltb (List.length (prev ++ [av])) (List.length ps)) with false
            by (symmetry; apply Nat.ltb_ge; rewrite app_length; cbn; lia).
          fuel K. rewrite (F.fwd_zip ps (prev ++ [av]) K) by lia.
          rewrite (G.zipb_combine ps (prev ++ [av])) by lia. rewrite G.apply_bound_zipped. apply E. lia. }
   all: exists (WRaise "not-callable"), 1; split; [|exact I]; intros K LK; fuel K;
     rewrite Q.apply_value_eq by (intros; discriminate); rewrite gate_ok by lia; reflexivity.
 - (* buri.eval-args *)
   intros es env k z g done e1 es' -> Ss Oe Lz H. inversion Ss as [|? ? Se Ss']; subst.
   destruct (CEn e1 env (KCallArgs g done (map R.tr es') (R.tr_env env) :: k) z Se Oe Lz H) as (w1 & F1 & E1 & D1 & O1 & G1).
   destruct w1 as [v|m| |]; try contradiction.
   + destruct es' as [|e2 es''].
     * exists (AVals [v]), (F1 + 3). split; [|split; [constructor; [exact O1|constructor]|reflexivity]].
       intros K LK. fuel K. rewrite Q.args_cons, (E1 K) by lia. fuel K. rewrite Q.args_first. fuel K.
       rewrite Q.args_nil, Q.args_rest. reflexivity.
     * pose proof (G1 (KCallArgs g done (map R.tr (e2 :: es'')) (R.tr_env env) :: k)) as T1. cbn [X.reaches2] in T1.
       destruct (halts_taus _ _ _ _ H T1) as (j1 & L1 & H1). hstep H1.
       match type of H1 with halts _ _ ?m1 =>
       pose proof (IG m1 ltac:(lia) (e2 :: es'') env k z g (R.tr_rv v :: done) e2 es'' eq_refl Ss' Oe ltac:(lia) H1)
         as (a2 & F2 & E2 & D2) end.
       destruct a2 as [vs|w2].
       -- destruct D2 as [Ovs Lvs]. exists (AVals (v :: vs)), (F1 + F2 + 3).
          split; [|split; [constructor; assumption|cbn in Lvs |- *; lia]].
          intros K LK. fuel K. rewrite Q.args_cons, (E1 K) by lia. fuel K. rewrite Q.args_first, (E2 K) by lia.
          fuel K. rewrite Q.args_rest. reflexivity.
       -- exists (AFail w2), (F1 + F2 + 3). split; [|exact D2].
          intros K LK. fuel K. rewrite Q.args_cons, (E1 K) by lia. fuel K. rewrite Q.args_first, (E2 K) by lia.
          fuel K. rewrite Q.args_rest. reflexivity.
   + exists (AFail (WRaise m)), (F1 + 2). split; [|exact I].
     intros K LK. fuel K. rewrite Q.args_cons, (E1 K) by lia. fuel K. rewrite Q.args_first. reflexivity.
Qed.
Lemma main_all : forall n, CE n /\ CA n /\ CG n.
Proof.
 intro n; induction n as [n IHn] using (well_founded_induction lt_wf). apply main. exact IHn.
Qed.
End Main.

(* E2E-07 completeness. For every well-formed definition table and every term
   of the extended subset, under every pinned profile and store: if the
   KLambda run of tr e terminates silently within m steps with outcome o
   (KLMetatheory.run returns VDone [] o), then for every budget z > m the
   actual Native evaluator running the captured buri.eval, with enough fuel,
   returns [returned v] where o = Normal (tr_rv v), or [raised msg] where
   o = Error x of the class of msg; never exhaustion or unsupported. *)
Theorem klambda_complete : forall ds e P s m o, X.ds_ok ds -> X.sub2 e -> X.pure2 P -> R.prims s -> X.defs s ds ->
 R.krun P m (Cfg (Eval [] (R.tr e)) [] s) tt = VDone [] o ->
 forall z, (Z.of_nat m < z)%Z ->
 exists w n0, (forall n, n0 <= n -> Native.Native.run n program "kl:buri.eval"
     [G.enc_defs ds; enc_term e; enc_env []; Native.Native.Integer z] = Native.Native.Returned (enc_verdict w)) /\
   match w with
   | WRet v => o = Normal (R.tr_rv v)
   | WRaise msg => exists x, o = Error x /\ X.exn2 msg x
   | _ => False end.
Proof.
 intros ds e P s m o Hds Se HP Hs Hd Run z Lz.
 destruct (krun_halts P m _ o Run) as (n & Ln & H).
 destruct (main_all ds P s Hds HP Hs Hd n) as [CEn _].
 destruct (CEn e [] [] z Se (Forall_nil _) ltac:(lia) H) as (w & F0 & E & Dw & _ & Gw).
 destruct (ask_run F0 _ _ _ (E F0 (le_n _))) as [n0 N0].
 exists w, n0. split; [exact N0|].
 pose proof (Gw []) as Rw.
 assert (Same : forall m' o', R.krun P m' (Cfg (Eval [] (R.tr e)) [] s) tt = VDone [] o' -> o' = o).
 { intros m' o' R'. pose proof (KLMetatheory.KLMetatheory.run_monotone unit R.env_none R.quiet R.still P m (m + m')
     (Cfg (Eval [] (R.tr e)) [] s) tt ltac:(lia)) as M1.
   pose proof (KLMetatheory.KLMetatheory.run_monotone unit R.env_none R.quiet R.still P m' (m + m')
     (Cfg (Eval [] (R.tr e)) [] s) tt ltac:(lia)) as M2.
   unfold R.krun in Run, R'. rewrite Run in M1. rewrite R' in M2.
   specialize (M1 I). specialize (M2 I). rewrite M1 in M2. injection M2 as ->. reflexivity. }
 destruct w as [v|msg| |]; cbn in Dw, Rw |- *; try contradiction.
 - destruct (R.taus_run P _ _ (Normal (R.tr_rv v)) Rw eq_refl) as [m' K]. symmetry. exact (Same m' _ K).
 - destruct Rw as (x & Cx & T). destruct (R.taus_run P _ _ (Error x) T eq_refl) as [m' K].
   exists x; split; [symmetry; exact (Same m' _ K)|exact Cx].
Qed.
End KLambdaEvaluatorComplete.
