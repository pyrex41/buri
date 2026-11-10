(* OB-JIT-EQ-BUDGET-CORE, the assembly: eq_core_statement and JitLowerEquiv.eq_budget_statement,
   proved from the base case (JitEqBudgetWalk.walk_bound) and the step (JitEqBudgetStep.step_settled)
   by induction on the size of a closed set of cells. No axioms.

   Proved here:
   - core_settled: for num_cmp P PEqual symmetric and transitive, a heap h and a NoDup list cs of
     cells closed in h (JitEqBudgetStep.closed_in: each cell of cs is allocated and the vector
     pointers in its data lie in cs), every pair of distinct cells of cs is settled at budget
     length cs: an answer of cellcmp at any budget is the answer at length cs.
   - eq_budget_closed: eq_budget_closed_statement, the same for two operands whose vector
     pointers (in their data) lie in cs: = at every budget >= S (length cs) answers what it answers
     at S (length cs). There is no global lok and no lok at all: cells outside cs are never read.
   - eq_core: eq_core_statement (jit_rules sealed), the corollary with cs = all cells
     (seq 0 (length h)), closed by the global lok of the statement's hypotheses.
   - eq_budget: JitLowerEquiv.eq_budget_statement sealed, via JitEqBudget.eq_budget_from_core.

   Notes on the statement of eq_budget_closed.
   - The operand form is at S (length cs), not length cs: = at budget 0 answers None for every
     pair, and with cs = [] (closed, NoDup) VNum 0 against VNum 0 answers Some true at budget 1.
     The cell form (cells_closed) is at length cs. This matches eq_budget_statement, which is at
     S (length h).
   - It takes no S-local lok (JitEqBudgetStep.lok_in): neither the step nor the base needs one, so
     the statement is stated without it, which is stronger.

   The case split. Whether some distinct pair of cs ever compares true is not decidable, and no
   excluded middle is used. The goal of `settled` at a given budget and answer is an equation on
   option bool, which is decidable; if it fails, any true pair met leads, through the step and
   the induction hypothesis, back to the goal, so the case without true pairs is the walk bound. *)
From Coq Require Import List Arith Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitProfile JitLowerEquiv
 JitEqBudget JitEqBudgetStep JitEqBudgetWalk.
Import ListNotations.
Module JitEqBudgetCore.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 KLPort.KLPort JitProfile.JitProfile JitEqBudget.JitEqBudget.
Module St := JitEqBudgetStep.JitEqBudgetStep.
Module Wk := JitEqBudgetWalk.JitEqBudgetWalk.
Local Open Scope nat_scope.

(* ======================= the two closure hypotheses agree ======================= *)
Lemma din_ptrs : forall (A : nat -> Prop) v l, St.din A v -> In l (Wk.data_ptrs v) -> A l.
Proof.
 intros A v l. induction v; cbn; intros D I; try contradiction.
 - destruct D as [Da Dd]. apply in_app_or in I as [I|I]; auto.
 - destruct I as [<-|[]]. exact D.
Qed.

Lemma closed_bridge : forall h cs, St.closed_in h cs -> Wk.closed_in h cs.
Proof.
 intros h cs C p xs Ip E l Il. destruct (C p Ip) as [ys [E' F]]. rewrite E in E'. injection E' as <-.
 apply in_flat_map in Il as [v [Iv Lv]]. rewrite Forall_forall in F. exact (din_ptrs _ v l (F v Iv) Lv).
Qed.

(* ======================= the induction on |cs| ======================= *)
Section Core.
Variables (R : port_rules) (P : profile).
Hypothesis Sy : forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x.
Hypothesis Tr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true.

Theorem core_settled : forall k h cs, NoDup cs -> St.closed_in h cs -> List.length cs = k ->
 forall p q, In p cs -> In q cs -> p <> q -> St.settled R P h k p q.
Proof.
 induction k as [|k IH]; intros h cs N C L p q Ip Iq D.
 - destruct cs; [destruct Ip|discriminate L].
 - intros d b H.
   assert (Dec : forall o : option bool, {o = Some b} + {o <> Some b})
     by (intro o; decide equality; apply Bool.bool_dec).
   destruct (Dec (cellcmp R P h (S k) p q)) as [G|Ne]; [exact G|exfalso; apply Ne].
   rewrite <- L. apply (Wk.walk_bound R P h cs Sy Tr (closed_bridge _ _ C)) with d; try assumption.
   intros d' p' q' Ip' Iq' D' T. apply Ne.
   destruct (St.least_true_exists R P h cs d' p' q' Ip' Iq' D' T) as [d0 [x [y Lt]]].
   pose proof Lt as Lt'. destruct Lt' as [Ix [Iy [Dxy _]]].
   destruct (St.closed_after h cs x y C Ix Dxy) as [C' _].
   assert (Hs : forall p1 q1, In p1 (remove Nat.eq_dec y cs) -> In q1 (remove Nat.eq_dec y cs) -> p1 <> q1 ->
     St.settled R P (St.surgery cs y x h) k p1 q1).
   { intros p1 q1 I1 J1 D1. apply (IH _ _ (St.remove_nodup y cs N) C'); auto.
     pose proof (St.remove_length y cs N Iy). lia. }
   exact (St.step_settled R P h cs d0 x y k (conj Sy Tr) C Lt Hs p q Ip Iq D d b H).
Qed.

(* The cell form: past length cs, more budget changes no comparison of two distinct cells of cs. *)
Theorem cells_closed : forall h cs, NoDup cs -> St.closed_in h cs ->
 forall p q, In p cs -> In q cs -> p <> q -> forall d, List.length cs <= d ->
 cellcmp R P h d p q = cellcmp R P h (List.length cs) p q.
Proof.
 intros h cs N C p q Ip Iq D d L.
 pose proof (core_settled _ h cs N C eq_refl p q Ip Iq D) as Hs.
 destruct (cellcmp R P h (List.length cs) p q) as [c|] eqn:E0.
 - exact (Wk.cellcmp_mono R P h _ d p q c L E0).
 - destruct (cellcmp R P h d p q) as [c|] eqn:E1; [|reflexivity].
   rewrite (Hs d c E1) in E0. discriminate E0.
Qed.
End Core.

(* = at S d reads two operands whose pointers satisfy A only through cellcmp d on A-cells. *)
Lemma eq_depth_same_in : forall R P h (A : nat -> Prop) d d',
 (forall p q, A p -> A q -> p <> q -> cellcmp R P h d p q = cellcmp R P h d' p q) ->
 forall a b, St.din A a -> St.din A b -> eq_depth_r R P h (S d) a b = eq_depth_r R P h (S d') a b.
Proof.
 intros R P h A d d' Hc a.
 induction a as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex]; intros w Da Dw;
  destruct w as [n'|s'|bb'|t'| |b1 b2|l0|st'|x1 e2 r2|e3 r3|f1 args1|ex']; try reflexivity.
 - destruct Da as [Da1 Da2]. destruct Dw as [Dw1 Dw2].
   change (match eq_depth_r R P h (S d) a1 b1 with Some true => eq_depth_r R P h (S d) a2 b2 | r => r end
         = match eq_depth_r R P h (S d') a1 b1 with Some true => eq_depth_r R P h (S d') a2 b2 | r => r end).
   rewrite (IHa1 b1 Da1 Dw1), (IHa2 b2 Da2 Dw2). reflexivity.
 - cbn. destruct (Nat.eqb_spec l l0) as [_|Dl]; [reflexivity|]. exact (Hc l l0 Da Dw Dl).
Qed.

(* ======================= the published statements ======================= *)
Definition eq_budget_closed_statement (R : port_rules) : Prop := forall P h cs,
 (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->
 (forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true) ->
 NoDup cs -> St.closed_in h cs ->
 forall a b, St.din (fun l => In l cs) a -> St.din (fun l => In l cs) b ->
 forall d, S (List.length cs) <= d -> eq_depth_r R P h d a b = eq_depth_r R P h (S (List.length cs)) a b.

Theorem eq_budget_closed : forall R, eq_budget_closed_statement R.
Proof.
 intros R P h cs Sy Tr N C a b Da Db d L. destruct d as [|d]; [lia|].
 apply (eq_depth_same_in R P h (fun l => In l cs)); [|exact Da|exact Db].
 intros p q Ip Iq D. apply (cells_closed R P Sy Tr h cs N C p q Ip Iq D). lia.
Qed.

(* All cells, closed by the global lok. *)
Lemma vok_din : forall n v, vok n v -> St.din (fun l => In l (seq 0 n)) v.
Proof.
 intros n v. induction v; cbn; try (intros; exact I).
 - intros [A B]. auto.
 - intro L. apply in_seq. lia.
Qed.

Lemma all_closed : forall h, Forall (lok (List.length h)) h -> St.closed_in h (seq 0 (List.length h)).
Proof.
 intros h Hh p Ip. apply in_seq in Ip.
 destruct (nth_error h p) as [xs|] eqn:E; [|apply nth_error_None in E; lia].
 exists xs. split; [reflexivity|].
 rewrite Forall_forall in Hh. pose proof (Hh xs (nth_error_In h p E)) as Lx.
 eapply Forall_impl; [|exact Lx]. apply vok_din.
Qed.

Lemma eq_core_all : forall R, eq_core_statement R.
Proof.
 intros R P' h Sy Tr Hh p q D.
 destruct (Nat.lt_ge_cases p (List.length h)) as [Lp|Lp];
 [destruct (Nat.lt_ge_cases q (List.length h)) as [Lq|Lq]|].
 - pose proof (cells_closed R P' Sy Tr h (seq 0 (List.length h)) (seq_NoDup _ _) (all_closed h Hh)
     p q (proj2 (in_seq _ _ _) (conj (Nat.le_0_l p) Lp)) (proj2 (in_seq _ _ _) (conj (Nat.le_0_l q) Lq)) D)
     as Hc.
   rewrite length_seq in Hc. symmetry. apply Hc. lia.
 - unfold cellcmp. rewrite (proj2 (nth_error_None h q) Lq). destruct (nth_error h p); reflexivity.
 - unfold cellcmp. rewrite (proj2 (nth_error_None h p) Lp). reflexivity.
Qed.

Theorem eq_core : forall sealed, eq_core_statement (jit_rules sealed).
Proof. intro sealed. exact (eq_core_all (jit_rules sealed)). Qed.

Theorem eq_budget : forall sealed, JitLowerEquiv.JitLowerEquiv.eq_budget_statement sealed.
Proof. intro sealed. exact (eq_budget_from_core sealed (eq_core sealed)). Qed.

End JitEqBudgetCore.
