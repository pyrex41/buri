(* = and its budget (JitLowerEquiv.eq_budget_statement, OB-JIT-EQ-BUDGET-CORE).

   Proved here, with no axioms:
   - jit_eq_per: JitLowerEquiv.jit_eq_per_statement. Under jit_profile, = on numbers is
     symmetric and transitive. It is not reflexive, because NaN equals nothing.
   - eq_budget_from_core: JitLowerEquiv.eq_budget_statement follows from eq_core_statement.
   - eq_depth_mono_le: more budget never takes back a defined answer.
   - eq_budget_refuted: without its two hypotheses the statement is false (below).
   eq_core_statement is proved in JitEqBudgetCore.v (JitEqBudgetCore.eq_core), from the step in
   JitEqBudgetStep.v and the base in JitEqBudgetWalk.v; JitEqBudgetCore.eq_budget is
   JitLowerEquiv.eq_budget_statement. This file does not import them. The paper proof below is
   kept as the plan they follow.

   ---- The core ----
   eq_core_statement: at budget length h, one more budget changes no comparison of two
   cells.

   Paper proof, formalized in JitEqBudgetStep.v, JitEqBudgetWalk.v and JitEqBudgetCore.v. Write
   K_d(p,q) for cellcmp d p q, and tau(p,q) for the least d at which it is Some, if any. By
   eq_depth_mono, the core says tau(p,q) <= length h. Prove,
   for every set S of cells closed under the vector pointers in their data (not closure
   environments: = never reads those) and all p, q in S, that tau(p,q) <= |S|. Induction on |S|:

   - Step: some distinct x, y in S have K_d(x,y) = Some true for some d. Take such a pair with
     the least d. Then the vector pointers in x and y's data are pairwise identical (a distinct
     true pair below them would have a smaller d). Every other leaf pair answers Some true,
     which is all = ever learns from it (numbers by the PER, closures by their ids). So
     replacing x's contents by y's leaves every comparison unchanged. Let h' redirect every
     VVec y in the data of S to VVec x. Then S - {y} is closed in h'. Same-budget simulation:
     where h' meets VVec x on both sides, h meets x against y, so h' answers the same as h
     at the same budget, or more often. Shifted simulation: h at budget d+1 answers at least
     what h' answers at budget d, the extra step paying for the one comparison of x with y. So
     tau_h <= tau_h' + 1 <= (|S| - 1) + 1.
   - Base: no two distinct cells of S ever compare true. Then a comparison with a Some answer
     is a single walk e_0, e_1, ..., e_L of cell pairs. Each step goes through the first leaf
     pair that disagrees, and tau(e_0) <= L + 1. Let pos(u,v) be the path, in depth-first
     order, at which comparing u with v stops, or infinity if it never stops. Agreement of
     leaves is a PER: number equality, closure ids, pointer identity. So for distinct u, v, w,
     the two smaller of pos(u,v), pos(v,w), pos(u,w) are equal. Hence, for each threshold t,
     "u = v or pos(u,v) > t" is an equivalence. The e_i have distinct pos, since pos(e_i) is
     one index longer than pos(e_(i+1)). Sort them and take each as the threshold in turn.
     Each split refines the partition of S strictly, so L + 2 <= |S|.

   The search suggests the bound is one better than this. Formalizing it needs depth-first
   positions over cyclic heaps, the ultrametric lemma, counting classes of equivalences on
   finite sets, and the heap-surgery simulation.

   The first sketch of this proof had two gaps. The argument above closes both on paper:
   - Pairs that answer true were counted on their own, and walks to a difference on their own.
     But a walk to a false answer can compare true sub-pairs along the way, and the two depths
     can add up to about 2 (length h). The step above removes true pairs one cell at a time, so
     the base only ever sees walks.
   - The first sketch measured the first difference in the unfolded trees of two cells. But
     "answers true" is not equality of unfolded trees: two pointers to one cell holding NaN
     compare true by the pointer shortcut, while two copies of it compare false. The base
     above measures positions in the comparison itself, which takes the shortcut. Its leaf
     agreement (number equality, closure ids, pointer identity) is a PER.

   ---- Without the hypotheses ----
   Without its two hypotheses on number equality, JitLowerEquiv.eq_budget_statement is false:
   past the budget S (length h), more budget can still change what = answers, here from None to
   Some false. `eq_budget_old_statement` is the statement without them, as it was at 818fd86.

   The statement quantifies over every profile P', and a profile's equality on inexact numbers
   (inexact_cmp P' PEqual) is any boolean function. `tol` below takes it to be a tolerance,
   |x - y| <= 1 on float bit patterns: reflexive and symmetric, but not transitive (0 ~ 1 and
   1 ~ 2, but not 0 ~ 2).

   The heap has five cells. Each holds a number and a pointer, so = compares the two numbers
   and then follows the two pointers:
     0 : [0; ->3]    3 : [2; ->0]      (a 2-cycle)
     1 : [1; ->2]    2 : [1; ->4]    4 : [2; ->1]      (a 3-cycle)
   Comparing cells 1 and 3 walks through the pairs (1,3) (2,0) (4,3) (1,0) (2,3) (4,0). The labels
   agree under `tol` until (4,0) compares 2 with 0. Six pairs need budget 7, but
   kl_eq_r's budget is S 5 = 6. With a partial equivalence (symmetric and transitive), labels
   that agree with a common label agree with each other, and Moore's bound applies to this
   functional walk. Without that, the walk around two coprime cycles can run up to their
   product. Transitivity alone is not enough: a search also found transitive, non-symmetric
   equalities that need more than S (length h). *)
From Coq Require Import List ZArith NArith Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitFloat JitProfile JitLowerEquiv.
Import ListNotations.
Module JitEqBudget.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 KLPort.KLPort JitProfile.JitProfile.
Module F := JitFloat.JitFloat.

Definition tol_cmp (_ : prim) (a b : num) : bool := match a, b with
 | NFloat x, NFloat y => (N.leb x (y + 1) && N.leb y (x + 1))%bool
 | _, _ => false end.

Definition tol : profile := Profile
 (inexact_op jit_profile) tol_cmp (int_div_inexact jit_profile) (float_text jit_profile)
 (str_other jit_profile) (sys_message jit_profile) (absvector_fill jit_profile)
 (time_value jit_profile) (stack_limit jit_profile) (heap_limit jit_profile).

Definition cell (label : N) (next : nat) : list value := [VNum (NFloat label); VVec next].
Definition h5 : list (list value) := [cell 0 3; cell 1 2; cell 1 4; cell 2 0; cell 2 1].

Lemma h5_ok : Forall (lok (List.length h5)) h5.
Proof. repeat constructor; cbn; lia. Qed.

(* The answers at budgets 6 and 7. Neither depends on the port rules: no closure is compared. *)
Lemma at_budget_6 : forall R, eq_depth_r R tol h5 6 (VVec 1) (VVec 3) = None.
Proof. intro R. vm_compute. reflexivity. Qed.
Lemma at_budget_7 : forall R, eq_depth_r R tol h5 7 (VVec 1) (VVec 3) = Some false.
Proof. intro R. vm_compute. reflexivity. Qed.
Lemma kl_eq_h5 : forall R, kl_eq_r R tol h5 (VVec 1) (VVec 3) = None.
Proof. intro R. exact (at_budget_6 R). Qed.

Definition eq_budget_old_statement (R : port_rules) : Prop := forall P' h d a b,
 Forall (lok (List.length h)) h -> vok (List.length h) a -> vok (List.length h) b ->
 (S (List.length h) <= d)%nat -> eq_depth_r R P' h d a b = kl_eq_r R P' h a b.

Theorem eq_budget_refuted : forall R, ~ eq_budget_old_statement R.
Proof.
 intros R H.
 specialize (H tol h5 7 (VVec 1) (VVec 3) h5_ok).
 assert (E : eq_depth_r R tol h5 7 (VVec 1) (VVec 3) = kl_eq_r R tol h5 (VVec 1) (VVec 3))
   by (apply H; cbn; lia).
 rewrite at_budget_7, kl_eq_h5 in E. discriminate E.
Qed.

(* `tol` is symmetric, so what the counterexample breaks is transitivity, the second of the
   hypotheses JitLowerEquiv.eq_budget_statement now takes. *)
Lemma tol_symmetric : forall x y, num_cmp tol PEqual x y = num_cmp tol PEqual y x.
Proof.
 intros [x|x] [y|y]; cbn; try reflexivity.
 - apply Z.eqb_sym.
 - apply andb_comm.
Qed.
Lemma tol_not_transitive :
 num_cmp tol PEqual (NFloat 0) (NFloat 1) = true /\ num_cmp tol PEqual (NFloat 1) (NFloat 2) = true /\
 num_cmp tol PEqual (NFloat 0) (NFloat 2) = false.
Proof. vm_compute. repeat split. Qed.

(* What does hold for every profile: on one heap, more budget never takes back a defined
   answer. It cannot turn Some into None or change which Some, because an answer is defined
   only if every comparison it reads is defined. The reverse fails (h5 above): a None at a
   smaller budget can become Some at a larger one. Carrying this to two related heaps needs
   more, which is not proved here: a lemma that = answers the same at equal budgets on heaps
   related by a location bijection whose extra cells = never reads. That only helps when the
   side with the larger heap may answer where the other answers None. *)
Lemma list_eq_mono : forall (f g : value -> value -> option bool),
 (forall u v y, f u v = Some y -> g u v = Some y) ->
 forall xs ys y, list_eq f xs ys = Some y -> list_eq g xs ys = Some y.
Proof.
 intros f g Hfg. induction xs as [|u xs IH]; intros [|v ys] y H; cbn in *; try exact H.
 destruct (f u v) as [[|]|] eqn:E; try discriminate H.
 - rewrite (Hfg _ _ _ E). exact (IH _ _ H).
 - rewrite (Hfg _ _ _ E). exact H.
Qed.

Lemma eq_depth_mono : forall R P h d a b y,
 eq_depth_r R P h d a b = Some y -> eq_depth_r R P h (S d) a b = Some y.
Proof.
 intros R P h. induction d as [|d IHd]; intros a b y H; [discriminate H|].
 revert b y H.
 induction a as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex]; intros w y H;
  destruct w as [n'|s'|bb'|t'| |b1 b2|l0|st'|x1 e2 r2|e3 r3|f1 args1|ex']; try exact H.
 - (* VCons *)
   change (match eq_depth_r R P h (S d) a1 b1 with Some true => eq_depth_r R P h (S d) a2 b2 | r => r end
           = Some y) in H.
   change (match eq_depth_r R P h (S (S d)) a1 b1 with Some true => eq_depth_r R P h (S (S d)) a2 b2 | r => r end
           = Some y).
   destruct (eq_depth_r R P h (S d) a1 b1) as [[|]|] eqn:E; try discriminate H.
   + rewrite (IHa1 _ _ E). exact (IHa2 _ _ H).
   + rewrite (IHa1 _ _ E). exact H.
 - (* VVec *)
   cbn in H |- *. destruct (Nat.eqb l l0); [exact H|].
   destruct (nth_error h l), (nth_error h l0); try discriminate H.
   exact (list_eq_mono _ _ IHd _ _ _ H).
Qed.

Lemma eq_depth_mono_le : forall R P h d d' a b y, (d <= d')%nat ->
 eq_depth_r R P h d a b = Some y -> eq_depth_r R P h d' a b = Some y.
Proof. intros R P h d d' a b y L. induction L; intro H; [exact H|]. apply eq_depth_mono. auto. Qed.

(* ======================= the revised statements ======================= *)
(* JitLowerEquiv.jit_eq_per_statement: proved below as jit_eq_per. *)

Section PerZ.
Local Open Scope Z_scope.
(* ======================= = on numbers under jit_profile is a PER ======================= *)
(* Every number that = can relate gets a key: an infinity its sign, a finite value (zeros
   included) its exact value times 2^1074, an integer in the scale. Finite doubles have
   exponent at least -1074, so the scaled value is an integer. NaN has no key. *)
(* The scale, kept opaque so that no tactic expands 2^1074. *)
Definition sc : Z := 1074.
Lemma sc_eq : sc = 1074. Proof. reflexivity. Qed.
Lemma sc_nonneg : 0 <= sc. Proof. unfold sc; lia. Qed.
Opaque sc.
Ltac slia := pose proof sc_eq; lia.
Definition fval (b : N) : option (Z * Z) := match F.rank (F.classify b) with
 | None => None
 | Some (i, s, e) => Some (i, s * 2 ^ (e + sc)) end.
Definition nval (x : num) : option (Z * Z) := match x with
 | NInt i => Some (0, i * 2 ^ sc)
 | NFloat b => fval b end.

Lemma classify_fin_e : forall b n m e, F.classify b = F.CFin n m e -> -1074 <= e.
Proof.
 intros b n m e H. unfold F.classify in H. cbv zeta in H.
 remember (Z.land (Z.shiftr (Z.of_N b) 52) 2047) as ex eqn:Ex.
 remember (Z.land (Z.of_N b) 4503599627370495) as fr eqn:Fr.
 assert (X : 0 <= ex) by (subst ex; apply Z.land_nonneg; right; lia).
 clear Ex Fr.
 destruct (Z.eqb_spec ex 2047); [destruct (Z.eqb fr 0); discriminate H|].
 destruct (Z.eqb_spec ex 0).
 - destruct (Z.eqb fr 0); inversion H; lia.
 - injection H as _ _ <-. lia.
Qed.

Lemma rank_facts : forall b i s e, F.rank (F.classify b) = Some (i, s, e) ->
 (i <> 0 /\ s = 0 /\ e = 0) \/ (i = 0 /\ -1074 <= e).
Proof.
 intros b i s e H. destruct (F.classify b) as [|neg|neg|neg m e'] eqn:C; cbn in H;
  inversion H; subst.
 - left. destruct neg; lia.
 - right. lia.
 - right. split; [reflexivity|]. exact (classify_fin_e _ _ _ _ C).
Qed.

Lemma pow2_nz : forall k, 0 <= k -> 2 ^ k <> 0.
Proof. intros k K. apply Z.pow_nonzero; slia. Qed.

Lemma scale_eq : forall s1 e1 s2 e2, -1074 <= e1 -> -1074 <= e2 ->
 (s1 * Z.shiftl 1 (e1 - Z.min e1 e2) = s2 * Z.shiftl 1 (e2 - Z.min e1 e2) <->
  s1 * 2 ^ (e1 + sc) = s2 * 2 ^ (e2 + sc)).
Proof.
 intros s1 e1 s2 e2 H1 H2. rewrite !Z.shiftl_1_l.
 assert (Me : Z.min e1 e2 <= e1 /\ Z.min e1 e2 <= e2 /\ -1074 <= Z.min e1 e2) by lia.
 remember (Z.min e1 e2) as e eqn:Ee. clear Ee.
 assert (A : e1 + sc = (e1 - e) + (e + sc)) by slia.
 assert (B : e2 + sc = (e2 - e) + (e + sc)) by slia.
 rewrite A, B.
 rewrite (Z.pow_add_r 2 (e1 - e) (e + sc)) by slia.
 rewrite (Z.pow_add_r 2 (e2 - e) (e + sc)) by slia. rewrite !Z.mul_assoc.
 split; intro Q; [rewrite Q; reflexivity|].
 apply Z.mul_cancel_r in Q; [exact Q|]. apply pow2_nz; slia.
Qed.

Lemma jit_order_eq : forall c, jit_order PEqual c = true <-> c = Some Eq.
Proof. intros [[| |]|]; split; cbn; congruence. Qed.

Lemma float_eq : forall a b, F.compare a b = Some Eq <-> fval a = fval b /\ fval a <> None.
Proof.
 intros a b. unfold F.compare, fval.
 destruct (F.rank (F.classify a)) as [[[i1 s1] e1]|] eqn:Ra;
 destruct (F.rank (F.classify b)) as [[[i2 s2] e2]|] eqn:Rb;
  try (split; [discriminate | intros [Q N]; congruence]).
 apply rank_facts in Ra, Rb.
 destruct (Z.eqb_spec i1 i2) as [<-|D]; cbn [negb].
 - destruct (Z.eqb_spec i1 0) as [->|D]; cbn [negb].
   + destruct Ra as [[? _]|[_ E1]]; [slia|]. destruct Rb as [[? _]|[_ E2]]; [slia|].
     pose proof (scale_eq s1 e1 s2 e2 E1 E2) as SE. split.
     * intro Q. injection Q as Q. apply Z.compare_eq_iff, SE in Q. rewrite Q.
       split; [reflexivity|discriminate].
     * intros [Q _]. injection Q as Q. apply SE in Q. rewrite (proj2 (Z.compare_eq_iff _ _) Q).
       reflexivity.
   + destruct Ra as [[_ [-> ->]]|[? _]]; [|slia]. destruct Rb as [[_ [-> ->]]|[? _]]; [|slia].
     split; [intros _; split; [reflexivity|discriminate] | reflexivity].
 - split.
   + intro Q. injection Q as Q. apply Z.compare_eq_iff in Q. contradiction.
   + intros [Q _]. injection Q as Q _. contradiction.
Qed.


Lemma int_float_eq : forall i b,
 JitBytecode.JitBytecode.compare_fix_real i b = Some Eq <-> Some (0, i * 2 ^ sc) = fval b.
Proof.
 intros i b. unfold JitBytecode.JitBytecode.compare_fix_real, F.ratio, fval.
 destruct (F.classify b) as [|neg|neg|neg m e] eqn:C; cbn.
 - split; discriminate.
 - split; [destruct neg; discriminate | intro Q; injection Q as Q _; destruct neg; discriminate Q].
 - rewrite Z.mul_1_r. split.
   + intro Q. injection Q as Q. apply Z.compare_eq_iff in Q. destruct neg; subst; reflexivity.
   + intro Q. injection Q as Q. f_equal. apply Z.compare_eq_iff.
     apply Z.mul_eq_0 in Q. destruct Q as [->|Q]; [destruct neg; reflexivity|].
     exfalso. exact (pow2_nz sc sc_nonneg Q).
 - pose proof (classify_fin_e _ _ _ _ C) as E.
   destruct (Z.leb_spec 0 e) as [L|L];
    change (if neg then - ?n else ?n) with (F.snum neg n).
   + rewrite Z.mul_1_r, Z.shiftl_mul_pow2 by exact L.
     assert (S : F.snum neg (m * 2 ^ e) = F.snum neg m * 2 ^ e) by (destruct neg; cbn; ring).
     rewrite S, Z.pow_add_r, Z.mul_assoc by slia.
     split.
     * intro Q. injection Q as Q. apply Z.compare_eq_iff in Q. rewrite Q. reflexivity.
     * intro Q. injection Q as Q. f_equal. apply Z.compare_eq_iff.
       apply Z.mul_cancel_r in Q; [exact Q|apply pow2_nz; slia].
   + rewrite Z.shiftl_1_l.
     assert (K : 2 ^ sc = 2 ^ (- e) * 2 ^ (e + sc))
       by (rewrite <- Z.pow_add_r by slia; f_equal; slia).
     rewrite K, Z.mul_assoc. split.
     * intro Q. injection Q as Q. apply Z.compare_eq_iff in Q. rewrite Q. reflexivity.
     * intro Q. injection Q as Q. f_equal. apply Z.compare_eq_iff.
       apply Z.mul_cancel_r in Q; [exact Q|apply pow2_nz; slia].
Qed.

Theorem jit_num_eq_iff : forall x y,
 num_cmp jit_profile PEqual x y = true <-> nval x = nval y /\ nval x <> None.
Proof.
 intros [i|a] [j|b]; cbn [num_cmp nval]; cbn [inexact_cmp jit_profile]; unfold jit_inexact_cmp.
 - rewrite Z.eqb_eq. split.
   + intros ->. split; [reflexivity|discriminate].
   + intros [Q _]. injection Q as Q. apply Z.mul_cancel_r in Q; [exact Q|apply pow2_nz; slia].
 - rewrite jit_order_eq, int_float_eq. split; [intros Q; split; [exact Q|discriminate]|tauto].
 - rewrite jit_order_eq.
   assert (Fl : forall c, flip c = Some Eq <-> c = Some Eq) by (intros [[| |]|]; cbn; split; congruence).
   rewrite Fl, int_float_eq. split.
   + intro Q. rewrite <- Q. split; [reflexivity|discriminate].
   + intros [Q N]. symmetry. exact Q.
 - rewrite jit_order_eq. exact (float_eq a b).
Qed.

Theorem jit_eq_per : JitLowerEquiv.jit_eq_per_statement.
Proof.
 split.
 - intros x y. apply Bool.eq_iff_eq_true. rewrite !jit_num_eq_iff.
   split; intros [Q N]; (split; [symmetry; exact Q| rewrite <- Q; exact N]).
 - intros x y z. rewrite !jit_num_eq_iff. intros [Q1 N1] [Q2 N2]. split; [congruence|exact N1].
Qed.

(* The edges of it. *)
Definition nan : N := F.canonical_nan.
Definition neg_zero : N := 9223372036854775808%N.
Example nan_not_reflexive : num_cmp jit_profile PEqual (NFloat nan) (NFloat nan) = false.
Proof. vm_compute. reflexivity. Qed.
Example zeros_equal : num_cmp jit_profile PEqual (NFloat neg_zero) (NFloat 0) = true
  /\ num_cmp jit_profile PEqual (NInt 0) (NFloat neg_zero) = true.
Proof. vm_compute. split; reflexivity. Qed.
(* 2^53 + 1 is not a double: it differs from the double 2^53, which equals 2^53. *)
Example big_int_exact :
 num_cmp jit_profile PEqual (NInt 9007199254740993) (NFloat (F.of_Z 9007199254740992)) = false
 /\ num_cmp jit_profile PEqual (NInt 9007199254740992) (NFloat (F.of_Z 9007199254740992)) = true
 /\ num_cmp jit_profile PEqual (NFloat (F.of_Z 9007199254740993)) (NFloat (F.of_Z 9007199254740992)) = true.
Proof. vm_compute. repeat split. Qed.
End PerZ.

(* ======================= reduction to one step on cells ======================= *)
(* = at budget S d reads the heap only through `cellcmp d`: the comparison, at budget d, of the
   contents of two different cells. So once one more budget changes no cell comparison, no
   further budget changes anything. That step at d = length h is
   eq_core_statement, proved in JitEqBudgetCore.v. *)
Section Reduce.
Variables (R : port_rules) (P : profile) (h : list (list value)).
Local Open Scope nat_scope.

Definition cellcmp (d p q : nat) : option bool := match nth_error h p, nth_error h q with
 | Some xs, Some ys => list_eq (eq_depth_r R P h d) xs ys
 | _, _ => None end.

Lemma list_eq_ext : forall f g, (forall u v, f u v = g u v) ->
 forall xs ys, list_eq f xs ys = list_eq g xs ys.
Proof.
 intros f g E. induction xs as [|u xs IH]; intros [|v ys]; cbn; try reflexivity.
 rewrite E. destruct (g u v) as [[|]|]; try reflexivity. apply IH.
Qed.

Lemma eq_depth_same_cells : forall d d', (forall p q, p <> q -> cellcmp d p q = cellcmp d' p q) ->
 forall a b, eq_depth_r R P h (S d) a b = eq_depth_r R P h (S d') a b.
Proof.
 intros d d' Hc a.
 induction a as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex]; intro w;
  destruct w as [n'|s'|bb'|t'| |b1 b2|l0|st'|x1 e2 r2|e3 r3|f1 args1|ex']; try reflexivity.
 - change (match eq_depth_r R P h (S d) a1 b1 with Some true => eq_depth_r R P h (S d) a2 b2 | r => r end
         = match eq_depth_r R P h (S d') a1 b1 with Some true => eq_depth_r R P h (S d') a2 b2 | r => r end).
   rewrite IHa1, IHa2. reflexivity.
 - cbn. destruct (Nat.eqb_spec l l0) as [_|D]; [reflexivity|]. exact (Hc l l0 D).
Qed.

Lemma cellcmp_step : forall d d', (forall p q, p <> q -> cellcmp d p q = cellcmp d' p q) ->
 forall p q, cellcmp (S d) p q = cellcmp (S d') p q.
Proof.
 intros d d' Hc p q. unfold cellcmp at 1 2.
 destruct (nth_error h p), (nth_error h q); try reflexivity.
 apply list_eq_ext. intros u v. apply eq_depth_same_cells. exact Hc.
Qed.

Lemma cellcmp_stable : forall n, (forall p q, p <> q -> cellcmp n p q = cellcmp (S n) p q) ->
 forall k p q, p <> q -> cellcmp (k + n) p q = cellcmp n p q.
Proof.
 intros n Hn. induction k as [|k IH]; intros p q D; [reflexivity|].
 change (S k + n) with (S (k + n)).
 rewrite (cellcmp_step (k + n) n IH p q). symmetry. exact (Hn p q D).
Qed.

Theorem budget_from_step : forall n, (forall p q, p <> q -> cellcmp n p q = cellcmp (S n) p q) ->
 forall d a b, S n <= d -> eq_depth_r R P h d a b = eq_depth_r R P h (S n) a b.
Proof.
 intros n Hn d a b L. destruct d as [|d]; [lia|].
 apply eq_depth_same_cells. intros p q D.
 replace d with ((d - n) + n) by lia. exact (cellcmp_stable n Hn _ p q D).
Qed.
End Reduce.

(* The core (proved in JitEqBudgetCore.v as eq_core): at budget length h, one more budget changes no cell comparison. By
   eq_depth_mono it is enough that a cell comparison that ever answers Some does so by budget
   length h. A search (a Python copy of eq_depth_r, used only for search, n <= 6, with
   partial-equivalence atoms, NaN-like atoms, nested pairs and an opaque value) found every
   cell comparison settled by budget length h - 1, one step inside this.

   The paper argument for it is in the header of this file. *)
Definition eq_core_statement (R : port_rules) : Prop := forall P' h,
 (forall x y, num_cmp P' PEqual x y = num_cmp P' PEqual y x) ->
 (forall x y z, num_cmp P' PEqual x y = true -> num_cmp P' PEqual y z = true -> num_cmp P' PEqual x z = true) ->
 Forall (lok (List.length h)) h ->
 forall p q, p <> q -> cellcmp R P' h (List.length h) p q = cellcmp R P' h (S (List.length h)) p q.

Theorem eq_budget_from_core : forall sealed,
 eq_core_statement (jit_rules sealed) -> JitLowerEquiv.eq_budget_statement sealed.
Proof.
 intros sealed Core P' h d a b Sy Tr Hh _ _ L. unfold kl_eq_r.
 exact (budget_from_step (jit_rules sealed) P' h _ (Core P' h Sy Tr Hh) d a b L).
Qed.

End JitEqBudget.
