(* BURI/EQ-1, obligation EQ1-TERM: total correctness of the captured EQ-1
   acceptance kernel under the Native evaluator.

   The recursive drivers of shen/kernel.shen (check-steps, check-step-result,
   after-rewrite, check-cases, check-case-bound, check-theorem, bundle-h,
   bundle-next) and the guarded body of check-bundle terminate on every
   finite input whose numbers are integers ([idata]; the Native number
   primitives used by nat? are integer-only), returning the reference
   verdict. One traced symbolic run per captured body
   (EqualityInductionTrace); recursion is structural on the proof data:
   the step list for check-steps, the case list for check-cases, the theorem
   list for bundle-h. Combined with the partial-correctness theorems of
   EqualityInductionRefinement this is total correctness of the captured
   checker under Native: for every such input there is a fuel at which the
   captured check-bundle returns exactly r_check_bundle, and the result is
   stable for all larger fuel. The bound is existential (constructive), not a
   closed formula. Not addressed: Chez executing the capture (E2E-32), the
   guard semantics (EQ1-GUARD, still the stated [guard_model]), and inputs
   containing non-integer numbers (outside the Native numeric model; see
   [fraction_budget_unsupported]). *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeComposition EqualityInductionOracle EqualityInductionModel EqualityInductionSpecs
 EqualityInductionHelpers EqualityInductionKernel EqualityInductionDrivers EqualityInductionRefinement
 EqualityInductionTrace EqualityInductionTotalBase EqualityInductionTotalTerms.
Import ListNotations Native.Native.
Module EqualityInductionTermination.
Import EqualityInductionModel.EqualityInductionModel EqualityInductionSpecs.EqualityInductionSpecs
 EqualityInductionHelpers.EqualityInductionHelpers EqualityInductionKernel.EqualityInductionKernel
 EqualityInductionDrivers.EqualityInductionDrivers EqualityInductionRefinement.EqualityInductionRefinement
 EqualityInductionTrace.EqualityInductionTrace EqualityInductionTotalBase.EqualityInductionTotalBase
 EqualityInductionTotalTerms.EqualityInductionTotalTerms.
Open Scope string_scope.
#[local] Arguments String.eqb : simpl nomatch.
#[local] Arguments same : simpl nomatch.
#[local] Arguments Z.eqb : simpl nomatch.
#[local] Arguments Z.leb : simpl nomatch.
#[local] Arguments Z.geb : simpl nomatch.
#[local] Arguments Z.sub : simpl nomatch.

Ltac pc_drvn field := let n := fresh "n" in let v := fresh "v" in let R := fresh "R" in
 intros n v R; apply run_ask in R; eapply (field _ (drivers (S n))); exact R.
Lemma goal_kv : forall C l r, r_goal C l r = true -> kv C = true.
Proof. intros C l r H. exact (proj1 (goal_ok C l r H)). Qed.
Lemma goal_tml : forall C l r, r_goal C l r = true -> tm l = true.
Proof. intros C l r H. exact (proj1 (proj2 (goal_ok C l r H))). Qed.
Lemma goal_tmr : forall C l r, r_goal C l r = true -> tm r = true.
Proof. intros C l r H. exact (proj2 (proj2 (goal_ok C l r H))). Qed.
#[global] Hint Resolve goal_kv goal_tml goal_tmr : tdb.

(* ---------- check-steps / check-step-result / after-rewrite ---------- *)
Definition Pst steps := forall l r C hs ls n, idata steps = true -> kv C = true -> wfr hs = true -> wfr ls = true ->
 okcall ("kl:buri.check-steps",[l;r;steps;C;hs;ls;Integer n],r_steps l r steps C hs ls n).
Definition Paf steps := forall x r C hs ls n, idata steps = true -> kv C = true -> wfr hs = true -> wfr ls = true ->
 okcall ("kl:buri.after-rewrite",[x;r;steps;C;hs;ls;Integer n],after1 x r steps C hs ls n).
Definition Pcs steps := forall e path dir l r C hs ls n, idata path = true -> idata steps = true -> kv C = true ->
 wfr hs = true -> wfr ls = true ->
 okcall ("kl:buri.check-step-result",[e;path;dir;l;r;steps;C;hs;ls;Integer n],csr1 e path dir l r steps C hs ls n).
Lemma af_of : forall steps, Pst steps -> Paf steps.
Proof.
 intros steps P x r C hs ls n D1 D2 D3 D4. unfold Pst in P.
 tdef ltac:(pc_drvn d_after).
Qed.
Lemma cs_of : forall steps, Pst steps -> Pcs steps.
Proof.
 intros steps P. pose proof (af_of steps P) as A. unfold Paf in A. unfold Pst in P.
 intros e path dir l r C hs ls n D0 D1 D2 D3 D4. tdef ltac:(pc_drvn d_csr).
Qed.
Lemma csr_from : forall steps e path dir l r C hs ls n, Pst steps -> idata path = true -> idata steps = true -> kv C = true ->
 wfr hs = true -> wfr ls = true ->
 okcall ("kl:buri.check-step-result",[e;path;dir;l;r;steps;C;hs;ls;Integer n],csr1 e path dir l r steps C hs ls n).
Proof. intros. exact (cs_of steps H e path dir l r C hs ls n H0 H1 H2 H3 H4). Qed.
#[local] Hint Resolve csr_from : tdb.
Lemma ok_stepping : forall steps, Pst steps.
Proof.
 vind_tac; intros steps IH; unfold Pst; intros l r C hs ls n D1 D2 D3 D4.
 tdef ltac:(intros ? ? R; exact (native_steps _ _ _ _ _ _ _ _ _ R)).
Qed.
Lemma ok_steps : forall l r steps C hs ls n, idata steps = true -> kv C = true -> wfr hs = true -> wfr ls = true ->
 okcall ("kl:buri.check-steps",[l;r;steps;C;hs;ls;Integer n],r_steps l r steps C hs ls n).
Proof. intros l r steps. exact (ok_stepping steps l r). Qed.
#[global] Hint Resolve ok_steps : tdb.

(* ---------- check-cases / check-case-bound ---------- *)
Definition Pca cases := forall ctors X C l r ls n, idata cases = true -> kv C = true -> tm l = true -> tm r = true ->
 wfr ls = true -> okcall ("kl:buri.check-cases",[ctors;cases;X;C;l;r;ls;Integer n],r_cases ctors cases X C l r ls n).
Lemma bound_from : forall cases z ctor ctors names steps X C l r ls n, Pca cases -> zok z = true -> lst names = true ->
 idata steps = true -> idata cases = true -> kv C = true -> tm l = true -> tm r = true -> wfr ls = true ->
 okcall ("kl:buri.check-case-bound",[z;ctor;ctors;cases;names;steps;X;C;l;r;ls;Integer n],
   bound1 z ctor ctors cases names steps X C l r ls n).
Proof.
 intros cases z ctor ctors names steps X C l r ls n P Z0 N0 S0 I0 C0 L0 R0 W0. unfold Pca in P.
 tdef ltac:(pc_drvn d_bound).
Qed.
#[local] Hint Resolve bound_from : tdb.
Lemma ok_casing : forall cases, Pca cases.
Proof.
 vind_tac; intros cases IH; unfold Pca; intros ctors X C l r ls n D1 D2 D3 D4 D5.
 tdef ltac:(intros ? ? R; exact (native_cases _ _ _ _ _ _ _ _ _ _ R)).
Qed.
Lemma ok_cases : forall ctors cases X C l r ls n, idata cases = true -> kv C = true -> tm l = true -> tm r = true ->
 wfr ls = true -> okcall ("kl:buri.check-cases",[ctors;cases;X;C;l;r;ls;Integer n],r_cases ctors cases X C l r ls n).
Proof. intros ctors cases. exact (ok_casing cases ctors). Qed.
#[global] Hint Resolve ok_cases : tdb.

(* ---------- check-theorem ---------- *)
Lemma ok_theorem : forall C l r p ls n, idata p = true -> kv C = true -> tm l = true -> tm r = true -> wfr ls = true ->
 okcall ("kl:buri.check-theorem",[C;l;r;p;ls;Integer n],r_theorem C l r p ls n).
Proof.
 intros C l r p ls n D1 D2 D3 D4 D5. tdef ltac:(intros ? ? R; exact (native_theorem _ _ _ _ _ _ _ _ R)).
Qed.
#[global] Hint Resolve ok_theorem : tdb.

(* ---------- bundle-h / bundle-next ---------- *)
Definition Pbu b := forall ls n, idata b = true -> wfr ls = true ->
 okcall ("kl:buri.bundle-h",[b;ls;Integer n],r_bundle b ls n).
Lemma next_from : forall rest res name C l r ls n, Pbu rest -> idata rest = true -> wfr ls = true -> tm l = true -> tm r = true ->
 okcall ("kl:buri.bundle-next",[res;name;C;l;r;rest;ls;Integer n],next1 res name C l r rest ls n).
Proof.
 intros rest res name C l r ls n P D1 D2 D3 D4. unfold Pbu in P. tdef ltac:(pc_drvn d_next).
Qed.
#[local] Hint Resolve next_from : tdb.
Lemma ok_bundling : forall b, Pbu b.
Proof.
 vind_tac; intros b IH; unfold Pbu; intros ls n D1 D2.
 tdef ltac:(intros ? ? R; exact (native_bundle _ _ _ _ _ R)).
Qed.
Lemma ok_bundle : forall b ls n, idata b = true -> wfr ls = true ->
 okcall ("kl:buri.bundle-h",[b;ls;Integer n],r_bundle b ls n).
Proof. intro b. exact (ok_bundling b). Qed.
#[global] Hint Resolve ok_bundle : tdb.

(* ---------- the guarded body of check-bundle ---------- *)
Lemma guarded_term : forall T B N, idata B = true -> numok N = true -> Term oref (arguments p_cb [T;B;N]) g_cb.
Proof. intros T B N D1 D2. tterm g_cb. Qed.

(* Every finite bundle with integer-only numbers: the captured guarded body
   of check-bundle returns, under the actual Native evaluator, exactly the
   reference verdict, at some fuel and every larger one. *)
Theorem native_guarded_body_total : forall T B N, idata B = true -> numok N = true ->
 exists n, forall m, n <= m -> eval m (lookup program) (arguments p_cb [T;B;N]) g_cb = Returned (r_check_bundle T B N).
Proof.
 intros T B N D1 D2. pose proof (guarded_term T B N D1 D2) as G. unfold Term in G.
 destruct (stepT oref (arguments p_cb [T;B;N]) g_cb) as [[v cs]|] eqn:E; [|contradiction].
 assert (A : agree defined dn g_cb = true) by (vm_compute; reflexivity).
 destruct (traced oref g_cb _ v cs A E G) as [n R].
 pose proof (native_guarded_body _ _ _ _ _ R) as V. subst v.
 exists n. intros m L. exact (NativeComposition.eval_monotone _ _ _ _ _ R m L).
Qed.
(* Total correctness of the captured check-bundle under the guard contract:
   it always terminates with the reference verdict (so acceptance and
   rejection are decided), and what it accepts is valid in the standard model. *)
Theorem captured_check_bundle_total : forall T B N, idata B = true -> numok N = true ->
 exists n, forall m, n <= m -> captured_check_bundle m T B N = Returned (r_check_bundle T B N).
Proof.
 intros T B N D1 D2. destruct (native_guarded_body_total T B N D1 D2) as [n H].
 exists n. intros m L. unfold captured_check_bundle, guard_model. rewrite (H m L). reflexivity.
Qed.
Theorem captured_check_bundle_decides : forall T B N, idata B = true -> numok N = true ->
 exists n v, captured_check_bundle n T B N = Returned v /\ v = r_check_bundle T B N /\
  (forall out, v = accepted out -> same T theory_value = true /\ all_ok out).
Proof.
 intros T B N D1 D2. destruct (captured_check_bundle_total T B N D1 D2) as [n H].
 exists n, (r_check_bundle T B N). split; [exact (H n (le_n n))|split; [reflexivity|]].
 intros out E. apply (check_bundle_sound T B N). exact E.
Qed.
Theorem native_bundle_total : forall B ls z, idata B = true -> wfr ls = true ->
 exists n, run n program "kl:buri.bundle-h" [B;ls;Integer z] = Returned (r_bundle B ls z).
Proof. intros B ls z D1 D2. exact (ok_bundle B ls z D1 D2). Qed.
Theorem native_steps_total : forall l r steps C hs ls z, idata steps = true -> kv C = true -> wfr hs = true -> wfr ls = true ->
 exists n, run n program "kl:buri.check-steps" [l;r;steps;C;hs;ls;Integer z] = Returned (r_steps l r steps C hs ls z).
Proof. intros. exact (ok_steps l r steps C hs ls z H H0 H1 H2). Qed.

(* Ground derivation (one input, not a universal claim): a fractional budget
   with the loaded theory is outside the Native numeric model; the captured
   nat? reaches an unsupported primitive, so the domain condition [numok] is
   needed for the Native statement (Chez would raise and the guard reject). *)
Example fraction_budget_unsupported :
 eval 1000 (lookup program) (arguments p_cb [theory_value;Nil;Fraction 1 2]) g_cb = Unsupported.
Proof. vm_compute. reflexivity. Qed.
End EqualityInductionTermination.
