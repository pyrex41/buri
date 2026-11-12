(* The step of the = budget core (JitEqBudget.v, header, "Step"), formalized.

   Proved here, with no axioms, for one comparison step on a set of cells `cs`:
   - least_true_pointers (i): if x and y compare true at the least budget d at which any two
     distinct cells of cs compare true, then the vector pointers in x's and y's data are pairwise
     identical, and every other leaf pair agrees: list_eq leaf_eq xs ys = Some true.
   - closed_after (ii): after the surgery that redirects VVec y to VVec x in the data of cs,
     cs minus {y} is closed, and S-locally lok if cs was.
   - same_budget_sim (iii): an answer of h on cells p, q of cs is an answer of h' at the same
     budget on (rl p, rl q), where rl sends y to x and fixes every other cell, provided
     rl p <> rl q.
   - shifted_sim (iv): an answer of h' on (rl p, rl q) at budget d is an answer of h at budget
     S d on (p, q). On cs minus {y} this is tau_h(p,q) <= tau_h'(p,q) + 1; a pair of y with q
     is mapped to the pair of x with q.
   - xy_answers_true, xy_true_from_1 (with the y,x orientation): the one pair that rl merges,
     {x,y}, only ever answers Some true, and does so at every budget >= 1.
   - step_settled: the step of the induction, in tau-free form. If every pair of distinct cells
     of cs minus {y} is settled in h' at n (an answer at any budget is the answer at n), every
     pair of distinct cells of cs is settled in h at S n.
   Also, for eq-assembly: least_true_exists (a true pair gives a least one), remove_length and
   remove_nodup (|cs minus {y}| = |cs| - 1), surgery_length, surgery_in, surgery_out.

   Hypotheses are S-relativized only: `closed_in h cs` (each cell of cs is allocated and the
   vector pointers in its data are in cs) and, for (ii), `lok_in h cs` (each cell of cs is lok in
   h). There is no global lok: cells outside cs are untouched by the surgery and never read. The
   simulations (iii), (iv) and step_settled also take the two hypotheses eq_core_statement
   takes, symmetry and transitivity of num_cmp P PEqual; (i) and (ii) take neither.

   The data of a cell: the values = reads in it, through VCons only. Closure environments,
   partial application arguments and exceptions are not data: = reads a closure only through
   closure_id, and the surgery leaves closures, with their ids, unchanged.

   Why the shift is 1. Where h' meets VVec x against VVec x, an immediate Some true, h meets x
   against y, which costs what x against y needs. By (i), x against y answers Some true at budget
   1 (identical pointers stop at once, other leaves agree), so one more step pays for it.

   Not here: the base case (no two distinct cells of cs compare true) and the assembly of
   eq_core_statement from the base and this step. OB-JIT-EQ-BUDGET-CORE stays open. *)
From Coq Require Import List Arith NArith Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLPort JitEqBudget.
Import ListNotations.
Module JitEqBudgetStep.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLPort.KLPort.
Local Open Scope nat_scope.

Local Notation cellcmp := JitEqBudget.JitEqBudget.cellcmp.
#[local] Arguments eq_opaque_r : simpl never.
#[local] Arguments num_cmp : simpl never.

(* ======================= definitions ======================= *)
(* Every vector pointer in the data of v satisfies A. *)
Fixpoint din (A : nat -> Prop) (v : value) : Prop := match v with
 | VCons a b => din A a /\ din A b
 | VVec l => A l
 | _ => True end.

(* cs is closed in h: each of its cells is allocated and points, in its data, into cs. *)
Definition closed_in (h : list (list value)) (cs : list nat) : Prop :=
 forall p, In p cs -> exists xs, nth_error h p = Some xs /\ Forall (din (fun l => In l cs)) xs.
(* S-local lok: each cell of cs is lok in h. *)
Definition lok_in (h : list (list value)) (cs : list nat) : Prop :=
 forall p xs, In p cs -> nth_error h p = Some xs -> lok (List.length h) xs.

(* = with pointers compared by identity: what two leaves of data tell = on their own. *)
Fixpoint leaf_eq (R : port_rules) (P : profile) (a b : value) : option bool := match a, b with
 | VNum x, VNum y => Some (num_cmp P PEqual x y)
 | VSym x, VSym y | VStr x, VStr y => Some (text_eqb x y)
 | VBool x, VBool y => Some (Bool.eqb x y)
 | VNil, VNil => Some true
 | VCons a1 a2, VCons b1 b2 => match leaf_eq R P a1 b1 with Some true => leaf_eq R P a2 b2 | r => r end
 | VStream x, VStream y => Some (N.eqb x y)
 | VVec l1, VVec l2 => Some (Nat.eqb l1 l2)
 | (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _), _ => match b with
     | VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _ => eq_opaque_r R a b | _ => Some false end
 | _, (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _) => Some false
 | _, _ => Some false end.

(* The surgery: y becomes x, in the data of the cells of cs only. *)
Definition rl (y x l : nat) : nat := if Nat.eqb l y then x else l.
Fixpoint rd (y x : nat) (v : value) : value := match v with
 | VCons a b => VCons (rd y x a) (rd y x b)
 | VVec l => VVec (rl y x l)
 | v => v end.
Fixpoint surg_from (cs : list nat) (y x i : nat) (h : list (list value)) : list (list value) :=
 match h with
 | [] => []
 | c :: h => (if existsb (Nat.eqb i) cs then map (rd y x) c else c) :: surg_from cs y x (S i) h end.
Definition surgery cs y x h := surg_from cs y x 0 h.

Definition least_true R P h cs d x y : Prop :=
 In x cs /\ In y cs /\ x <> y /\ cellcmp R P h d x y = Some true /\
 forall d' p q, d' < d -> In p cs -> In q cs -> p <> q -> cellcmp R P h d' p q <> Some true.

(* An answer at any budget is the answer at n. *)
Definition settled R P h n p q : Prop :=
 forall d b, cellcmp R P h d p q = Some b -> cellcmp R P h n p q = Some b.

(* ======================= generic facts ======================= *)
Lemma list_eq_true : forall f xs ys,
 list_eq f xs ys = Some true <-> Forall2 (fun u v => f u v = Some true) xs ys.
Proof.
 intro f. induction xs as [|u xs IH]; intros [|v ys]; cbn; split; intro H; auto;
  try discriminate H; try (inversion H; fail).
 - destruct (f u v) as [[|]|] eqn:E; try discriminate H. constructor; [exact E|apply IH, H].
 - inversion H; subst. rewrite H3. apply IH. exact H5.
Qed.

Lemma list_lift : forall (f g : value -> value -> option bool) (t : value -> value) (A : value -> Prop),
 (forall u v b, A u -> A v -> f u v = Some b -> g (t u) (t v) = Some b) ->
 forall xs ys b, Forall A xs -> Forall A ys -> list_eq f xs ys = Some b -> list_eq g (map t xs) (map t ys) = Some b.
Proof.
 intros f g t A Hfg. induction xs as [|u xs IH]; intros [|v ys] b Hx Hy H; cbn in *; try exact H.
 inversion Hx as [|? ? Au Fx]; inversion Hy as [|? ? Av Fy]; subst.
 destruct (f u v) as [[|]|] eqn:E; try discriminate H.
 - rewrite (Hfg _ _ _ Au Av E). exact (IH _ _ Fx Fy H).
 - rewrite (Hfg _ _ _ Au Av E). exact H.
Qed.

Lemma list_unlift : forall (f g : value -> value -> option bool) (t : value -> value) (A : value -> Prop),
 (forall u v b, A u -> A v -> g (t u) (t v) = Some b -> f u v = Some b) ->
 forall xs ys b, Forall A xs -> Forall A ys -> list_eq g (map t xs) (map t ys) = Some b -> list_eq f xs ys = Some b.
Proof.
 intros f g t A Hfg. induction xs as [|u xs IH]; intros [|v ys] b Hx Hy H; cbn in *; try exact H.
 inversion Hx as [|? ? Au Fx]; inversion Hy as [|? ? Av Fy]; subst.
 destruct (g (t u) (t v)) as [[|]|] eqn:E; try discriminate H.
 - rewrite (Hfg _ _ _ Au Av E). exact (IH _ _ Fx Fy H).
 - rewrite (Hfg _ _ _ Au Av E). exact H.
Qed.

Lemma in_remove_iff : forall (y p : nat) l, In p (remove Nat.eq_dec y l) <-> In p l /\ p <> y.
Proof.
 intros y p. induction l as [|a l IH]; cbn; [tauto|].
 destruct (Nat.eq_dec y a) as [<-|D]; cbn; rewrite IH; split; intuition congruence.
Qed.

Lemma remove_notin : forall (y : nat) l, ~ In y l -> remove Nat.eq_dec y l = l.
Proof.
 intros y. induction l as [|a l IH]; intro N; cbn; [reflexivity|].
 destruct (Nat.eq_dec y a) as [E|D]; [exfalso; apply N; left; congruence|].
 f_equal. apply IH. intro J. apply N. right. exact J.
Qed.

Lemma remove_length : forall (y : nat) l, NoDup l -> In y l -> S (List.length (remove Nat.eq_dec y l)) = List.length l.
Proof.
 intros y. induction l as [|a l IH]; intros N I; [destruct I|]. inversion N as [|? ? Na Nl]; subst.
 cbn. destruct (Nat.eq_dec y a) as [E|D].
 - subst. rewrite remove_notin by exact Na. reflexivity.
 - cbn. f_equal. apply IH; [exact Nl|]. destruct I as [E|I]; [congruence|exact I].
Qed.

Lemma remove_nodup : forall (y : nat) l, NoDup l -> NoDup (remove Nat.eq_dec y l).
Proof.
 intros y. induction l as [|a l IH]; intro N; cbn; [constructor|]. inversion N as [|? ? Na Nl]; subst.
 destruct (Nat.eq_dec y a); [apply IH, Nl|]. constructor; [|apply IH, Nl].
 rewrite in_remove_iff. tauto.
Qed.

(* ======================= the surgery ======================= *)
Lemma nth_surg_from : forall cs y x h i n, nth_error (surg_from cs y x i h) n =
 option_map (fun c => if existsb (Nat.eqb (i + n)) cs then map (rd y x) c else c) (nth_error h n).
Proof.
 intros cs y x. induction h as [|c h IH]; intros i [|n]; cbn; try reflexivity.
 - rewrite Nat.add_0_r. reflexivity.
 - rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma in_existsb : forall p cs, In p cs <-> existsb (Nat.eqb p) cs = true.
Proof.
 intros p cs. rewrite existsb_exists. split.
 - intro I. exists p. rewrite Nat.eqb_refl. auto.
 - intros [q [I E]]. apply Nat.eqb_eq in E. subst. exact I.
Qed.

Theorem surgery_in : forall cs y x h p, In p cs ->
 nth_error (surgery cs y x h) p = option_map (map (rd y x)) (nth_error h p).
Proof.
 intros cs y x h p I. unfold surgery. rewrite nth_surg_from. cbn.
 apply in_existsb in I. rewrite I. reflexivity.
Qed.

Theorem surgery_out : forall cs y x h p, ~ In p cs -> nth_error (surgery cs y x h) p = nth_error h p.
Proof.
 intros cs y x h p I. unfold surgery. rewrite nth_surg_from. cbn.
 destruct (existsb (Nat.eqb p) cs) eqn:E; [apply in_existsb in E; contradiction|].
 destruct (nth_error h p); reflexivity.
Qed.

Theorem surgery_length : forall cs y x h, List.length (surgery cs y x h) = List.length h.
Proof.
 intros cs y x h. unfold surgery. generalize 0. induction h as [|c h IH]; intro i; cbn; auto.
Qed.

Lemma din_rd : forall cs y x v, In x cs -> x <> y -> din (fun l => In l cs) v ->
 din (fun l => In l (remove Nat.eq_dec y cs)) (rd y x v).
Proof.
 intros cs y x v Ix D. induction v; cbn; try tauto. intro I. rewrite in_remove_iff. unfold rl.
 destruct (Nat.eqb_spec l y); split; congruence.
Qed.

Lemma vok_rd : forall n y x v, x < n -> vok n v -> vok n (rd y x v).
Proof.
 intros n y x v X. induction v; cbn; try tauto. unfold rl. destruct (Nat.eqb l y); lia.
Qed.

(* (ii) *)
Theorem closed_after : forall h cs x y, closed_in h cs -> In x cs -> x <> y ->
 closed_in (surgery cs y x h) (remove Nat.eq_dec y cs) /\
 (lok_in h cs -> lok_in (surgery cs y x h) (remove Nat.eq_dec y cs)).
Proof.
 intros h cs x y C Ix D. split.
 - intros p Ip. apply in_remove_iff in Ip as [Ip _].
   destruct (C p Ip) as [xs [E F]]. exists (map (rd y x) xs).
   rewrite surgery_in, E by exact Ip. split; [reflexivity|].
   apply Forall_map. eapply Forall_impl; [|exact F]. intros v. apply din_rd; assumption.
 - intros L p xs Ip E. apply in_remove_iff in Ip as [Ip _].
   rewrite surgery_in in E by exact Ip. rewrite surgery_length.
   destruct (nth_error h p) as [ys|] eqn:Ey; [|discriminate E]. injection E as <-.
   assert (Xl : x < List.length h).
   { destruct (C x Ix) as [zs [Ez _]]. apply nth_error_Some. congruence. }
   apply Forall_map. eapply Forall_impl; [|exact (L p ys Ip Ey)]. intros v. apply vok_rd. exact Xl.
Qed.

(* ======================= = and its leaves ======================= *)
Section Leaves.
Variables (R : port_rules) (P : profile).
Local Notation E := (eq_depth_r R P).

Lemma eq_cons : forall H d a1 a2 b1 b2, E H (S d) (VCons a1 a2) (VCons b1 b2) =
 match E H (S d) a1 b1 with Some true => E H (S d) a2 b2 | r => r end.
Proof. reflexivity. Qed.
Lemma eq_vec : forall H d l1 l2, E H (S d) (VVec l1) (VVec l2) = if Nat.eqb l1 l2 then Some true else
 match nth_error H l1, nth_error H l2 with Some xs, Some ys => list_eq (E H d) xs ys | _, _ => None end.
Proof. reflexivity. Qed.

Lemma opaque_sym : forall a b, eq_opaque_r R a b = eq_opaque_r R b a.
Proof.
 intros a b. unfold eq_opaque_r. destruct (object_identity R); [|reflexivity].
 destruct a, b; cbn; try reflexivity;
  destruct (closure_id env), (closure_id env0); try reflexivity; rewrite Nat.eqb_sym; reflexivity.
Qed.

Lemma opaque_rep : forall a a' v, eq_opaque_r R a a' = Some true -> eq_opaque_r R a v = eq_opaque_r R a' v.
Proof.
 intros a a' v H. unfold eq_opaque_r in *. destruct (object_identity R); [|discriminate H].
 destruct a, a'; cbn in H; try discriminate H;
  destruct (closure_id env) as [i|] eqn:Ei, (closure_id env0) as [j|] eqn:Ej; try discriminate H;
  injection H as H; apply Nat.eqb_eq in H; subst;
  destruct v; cbn; rewrite ?Ei, ?Ej; reflexivity.
Qed.

Lemma leaf_true_eq : forall H d u v, leaf_eq R P u v = Some true -> E H (S d) u v = Some true.
Proof.
 intros H d u. induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v Hl; destruct v; cbn in Hl; try discriminate Hl.
 all: try (cbn; exact Hl).
 - rewrite eq_cons. destruct (leaf_eq R P a1 v1) as [[|]|] eqn:E1; try discriminate Hl.
   rewrite (IHa1 _ E1). exact (IHa2 _ Hl).
 - injection Hl as Hl. apply Nat.eqb_eq in Hl. subst. rewrite eq_vec, Nat.eqb_refl. reflexivity.
Qed.

Lemma leaf_rd : forall y x u v, leaf_eq R P u v = Some true -> leaf_eq R P (rd y x u) (rd y x v) = Some true.
Proof.
 intros y x u. induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v Hl; destruct v; cbn in Hl; try discriminate Hl; try (cbn; exact Hl).
 - cbn. destruct (leaf_eq R P a1 v1) as [[|]|] eqn:E1; try discriminate Hl.
   rewrite (IHa1 _ E1). exact (IHa2 _ Hl).
 - injection Hl as Hl. apply Nat.eqb_eq in Hl. subst. cbn. rewrite Nat.eqb_refl. reflexivity.
Qed.

Section Per.
Hypothesis Sy : forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x.
Hypothesis Tr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true.

Lemma num_rep : forall n n' m, num_cmp P PEqual n n' = true -> num_cmp P PEqual n m = num_cmp P PEqual n' m.
Proof.
 intros n n' m H. destruct (num_cmp P PEqual n m) eqn:A, (num_cmp P PEqual n' m) eqn:B; try reflexivity.
 - rewrite Sy in H. rewrite (Tr _ _ _ H A) in B. discriminate B.
 - rewrite (Tr _ _ _ H B) in A. discriminate A.
Qed.

Lemma leaf_sym : forall u v, leaf_eq R P u v = Some true -> leaf_eq R P v u = Some true.
Proof.
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v Hl; destruct v; cbn in Hl |- *; try discriminate Hl; try (rewrite opaque_sym; exact Hl).
 - rewrite Sy. exact Hl.
 - injection Hl as Hl. apply text_eqb_eq in Hl. subst. rewrite text_eqb_refl. reflexivity.
 - match goal with |- Some (Bool.eqb ?a ?c) = _ => destruct a, c; exact Hl end.
 - injection Hl as Hl. apply text_eqb_eq in Hl. subst. rewrite text_eqb_refl. reflexivity.
 - reflexivity.
 - destruct (leaf_eq R P a1 v1) as [[|]|] eqn:E1; try discriminate Hl.
   rewrite (IHa1 _ E1). exact (IHa2 _ Hl).
 - rewrite Nat.eqb_sym. exact Hl.
 - rewrite N.eqb_sym. exact Hl.
Qed.

(* Replacing a value by one whose leaves agree with it changes no comparison, on either side. *)
Lemma leaf_rep_l : forall H d u u' v, leaf_eq R P u u' = Some true -> E H d u v = E H d u' v.
Proof.
 intros H [|d]; [reflexivity|].
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros u' v Hl; destruct u'; cbn in Hl; try discriminate Hl.
 all: destruct v; try reflexivity.
 all: lazymatch goal with
  | |- E _ _ (VCons _ _) (VCons _ _) = _ =>
      rewrite !eq_cons; destruct (leaf_eq R P a1 u'1) as [[|]|] eqn:E1; try discriminate Hl;
      rewrite (IHa1 _ _ E1), (IHa2 _ _ Hl); reflexivity
  | _ => cbn
  end.
 all: try reflexivity; try (apply opaque_rep; exact Hl).
 all: try (injection Hl as Hl).
 all: try (f_equal; apply num_rep; exact Hl).
 all: try (apply text_eqb_eq in Hl; subst; reflexivity).
 all: try (apply Bool.eqb_prop in Hl; subst; reflexivity).
 all: try (apply N.eqb_eq in Hl; subst; reflexivity).
 all: try (apply Nat.eqb_eq in Hl; subst; reflexivity).
Qed.

Lemma leaf_rep_r : forall H d u v v', leaf_eq R P v v' = Some true -> E H d u v = E H d u v'.
Proof.
 intros H [|d]; [reflexivity|].
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v v' Hl; destruct v, v'; cbn in Hl; try discriminate Hl; try reflexivity.
 all: lazymatch goal with
  | |- E _ _ (VCons _ _) (VCons _ _) = _ =>
      rewrite !eq_cons; destruct (leaf_eq R P v1 v'1) as [[|]|] eqn:E1; try discriminate Hl;
      rewrite (IHa1 _ _ E1), (IHa2 _ _ Hl); reflexivity
  | _ => cbn
  end.
 all: try reflexivity.
 all: try (match goal with |- eq_opaque_r R ?a ?b = eq_opaque_r R ?a ?c =>
   rewrite (opaque_sym a b), (opaque_sym a c); apply opaque_rep; exact Hl end).
 all: try (injection Hl as Hl).
 all: try (f_equal; rewrite (Sy n), (Sy n); apply num_rep; exact Hl).
 all: try (apply text_eqb_eq in Hl; subst; reflexivity).
 all: try (apply Bool.eqb_prop in Hl; subst; reflexivity).
 all: try (apply N.eqb_eq in Hl; subst; reflexivity).
 all: try (apply Nat.eqb_eq in Hl; subst; reflexivity).
Qed.

Lemma list_rep_l : forall H d xs xs' ys, Forall2 (fun a a' => leaf_eq R P a a' = Some true) xs xs' ->
 list_eq (E H d) xs ys = list_eq (E H d) xs' ys.
Proof.
 intros H d xs xs' ys F. revert ys. induction F as [|a a' xs xs' Ha F IH]; intros [|v ys]; cbn; try reflexivity.
 rewrite (leaf_rep_l H d a a' v Ha). destruct (E H d a' v) as [[|]|]; auto.
Qed.

Lemma list_rep_r : forall H d xs ys ys', Forall2 (fun a a' => leaf_eq R P a a' = Some true) ys ys' ->
 list_eq (E H d) xs ys = list_eq (E H d) xs ys'.
Proof.
 intros H d xs ys ys' F. revert xs. induction F as [|a a' ys ys' Ha F IH]; intros [|u xs]; cbn; try reflexivity.
 rewrite (leaf_rep_r H d u a a' Ha). destruct (E H d u a') as [[|]|]; auto.
Qed.
End Per.
End Leaves.

(* ======================= (i) ======================= *)
Lemma leaf_of_least : forall R P h cs e u v,
 (forall p q, In p cs -> In q cs -> p <> q -> cellcmp R P h e p q <> Some true) ->
 din (fun l => In l cs) u -> din (fun l => In l cs) v ->
 eq_depth_r R P h (S e) u v = Some true -> leaf_eq R P u v = Some true.
Proof.
 intros R P h cs e u v Lst. revert v.
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v Du Dv H; destruct v; try (cbn in H |- *; exact H).
 - rewrite eq_cons in H. cbn in Du, Dv |- *.
   destruct (eq_depth_r R P h (S e) a1 v1) as [[|]|] eqn:E1; try discriminate H.
   rewrite (IHa1 _ (proj1 Du) (proj1 Dv) E1). exact (IHa2 _ (proj2 Du) (proj2 Dv) H).
 - cbn in Du, Dv |- *. rewrite eq_vec in H. destruct (Nat.eqb_spec l l0) as [<-|D]; [reflexivity|].
   exfalso. apply (Lst l l0 Du Dv D). unfold cellcmp.
   destruct (nth_error h l), (nth_error h l0); try discriminate H. exact H.
Qed.

(* (i). The 'least d' premise is the last one. *)
Theorem least_true_pointers : forall R P h cs d x y xs ys,
 closed_in h cs -> In x cs -> In y cs ->
 nth_error h x = Some xs -> nth_error h y = Some ys ->
 cellcmp R P h d x y = Some true ->
 (forall d' p q, d' < d -> In p cs -> In q cs -> p <> q -> cellcmp R P h d' p q <> Some true) ->
 list_eq (leaf_eq R P) xs ys = Some true.
Proof.
 intros R P h cs d x y xs ys C Ix Iy Ex Ey T Lst.
 unfold cellcmp in T. rewrite Ex, Ey in T. apply list_eq_true in T. apply list_eq_true.
 destruct (C x Ix) as [xs' [Ex' Fx]]. destruct (C y Iy) as [ys' [Ey' Fy]].
 rewrite Ex in Ex'. rewrite Ey in Ey'. injection Ex' as <-. injection Ey' as <-.
 destruct d as [|e].
 - inversion T as [|u v ? ? Huv]; [constructor|discriminate Huv].
 - clear Ex Ey. revert Fx Fy. induction T as [|u v xs ys Huv T IH]; intros Fx Fy; constructor;
    inversion Fx as [|? ? Du Fx']; inversion Fy as [|? ? Dv Fy']; subst.
   + exact (leaf_of_least R P h cs e u v (fun p q => Lst e p q (Nat.lt_succ_diag_r e)) Du Dv Huv).
   + apply IH; [exact Fx'|exact Fy'].
Qed.

(* ======================= the simulations ======================= *)
Section Sim.
Variables (R : port_rules) (P : profile) (h : list (list value)) (cs : list nat) (x y : nat) (X Y : list value).
Hypothesis Sy : forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x.
Hypothesis Tr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true.
Hypothesis C : closed_in h cs.
Hypothesis Ix : In x cs.
Hypothesis Iy : In y cs.
Hypothesis Dxy : x <> y.
Hypothesis Ex : nth_error h x = Some X.
Hypothesis Ey : nth_error h y = Some Y.
Hypothesis Ag : list_eq (leaf_eq R P) X Y = Some true.
Local Notation E := (eq_depth_r R P).
Local Notation h' := (surgery cs y x h).
Local Notation inC := (fun l => In l cs).
Local Notation rl := (rl y x).
Local Notation rd := (rd y x).

Lemma agree_rd : Forall2 (fun a a' => leaf_eq R P a a' = Some true) (map rd Y) (map rd X).
Proof.
 apply list_eq_true in Ag. clear -Ag Sy. induction Ag as [|a a' xs ys H F IH]; cbn; constructor; [|apply IH; assumption].
 apply leaf_rd, leaf_sym; assumption.
Qed.

Lemma xy_true : forall H d, list_eq (E H (S d)) X Y = Some true /\ list_eq (E H (S d)) Y X = Some true.
Proof.
 intros H d. apply list_eq_true in Ag. split; apply list_eq_true.
 - eapply Forall2_impl; [|exact Ag]. intros u v. apply leaf_true_eq.
 - clear -Ag Sy. induction Ag as [|a a' xs ys Ha F IH]; constructor; [|apply IH; assumption].
   apply leaf_true_eq, leaf_sym; assumption.
Qed.

Lemma fetch : forall l, In l cs -> exists A A', nth_error h l = Some A /\ nth_error h' (rl l) = Some A' /\
 Forall (din inC) A /\
 (forall H d zs, list_eq (E H d) A' zs = list_eq (E H d) (map rd A) zs) /\
 (forall H d zs, list_eq (E H d) zs A' = list_eq (E H d) zs (map rd A)).
Proof.
 intros l Il. destruct (C l Il) as [A [EA FA]]. exists A. unfold rl, JitEqBudgetStep.rl.
 destruct (Nat.eqb_spec l y) as [->|D].
 - exists (map rd X). rewrite surgery_in, Ex by exact Ix. rewrite Ey in EA. injection EA as <-.
   repeat split; auto; intros H d zs; symmetry.
   + apply list_rep_l; [exact Sy|exact Tr|exact agree_rd].
   + apply list_rep_r; [exact Sy|exact Tr|exact agree_rd].
 - exists (map rd A). rewrite surgery_in, EA by exact Il. repeat split; auto.
Qed.

Lemma rl_merge : forall l1 l2, l1 <> l2 -> rl l1 = rl l2 -> (l1 = x /\ l2 = y) \/ (l1 = y /\ l2 = x).
Proof.
 intros l1 l2 D. unfold JitEqBudgetStep.rl.
 destruct (Nat.eqb_spec l1 y), (Nat.eqb_spec l2 y); intro Q; subst; tauto.
Qed.

Lemma xy_some_true : forall d b, (list_eq (E h d) X Y = Some b \/ list_eq (E h d) Y X = Some b) -> b = true.
Proof.
 intros d b [H|H].
 - pose proof (JitEqBudget.JitEqBudget.list_eq_mono _ _ (JitEqBudget.JitEqBudget.eq_depth_mono R P h d) _ _ _ H) as M.
   rewrite (proj1 (xy_true h d)) in M. congruence.
 - pose proof (JitEqBudget.JitEqBudget.list_eq_mono _ _ (JitEqBudget.JitEqBudget.eq_depth_mono R P h d) _ _ _ H) as M.
   rewrite (proj2 (xy_true h d)) in M. congruence.
Qed.

(* Same-budget simulation, on values. *)
Lemma same_val : forall d u v b, din inC u -> din inC v ->
 E h d u v = Some b -> E h' d (rd u) (rd v) = Some b.
Proof.
 induction d as [|e IHe]; [discriminate|].
 assert (IL : forall xs ys b, Forall (din inC) xs -> Forall (din inC) ys ->
   list_eq (E h e) xs ys = Some b -> list_eq (E h' e) (map rd xs) (map rd ys) = Some b)
   by (apply list_lift; exact IHe).
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l1|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v b Du Dv H; destruct v; try (cbn in H |- *; exact H).
 - cbn [rd]. rewrite eq_cons in H |- *. cbn in Du, Dv.
   destruct (E h (S e) a1 v1) as [[|]|] eqn:E1; try discriminate H.
   + rewrite (IHa1 _ _ (proj1 Du) (proj1 Dv) E1). exact (IHa2 _ _ (proj2 Du) (proj2 Dv) H).
   + rewrite (IHa1 _ _ (proj1 Du) (proj1 Dv) E1). exact H.
 - cbn in Du, Dv. cbn [rd]. rewrite eq_vec in H |- *.
   destruct (Nat.eqb_spec l1 l) as [<-|D]; [rewrite Nat.eqb_refl; exact H|].
   destruct (fetch l1 Du) as [A1 [A1' [F1 [G1 [D1 [L1 _]]]]]].
   destruct (fetch l Dv) as [A2 [A2' [F2 [G2 [D2 [_ R2]]]]]].
   rewrite F1, F2 in H.
   destruct (Nat.eqb_spec (rl l1) (rl l)) as [Q|Q].
   + destruct (rl_merge l1 l D Q) as [[-> ->]|[-> ->]].
     * rewrite Ex in F1. rewrite Ey in F2. injection F1 as <-. injection F2 as <-.
       rewrite (xy_some_true e b (or_introl H)) in H |- *. reflexivity.
     * rewrite Ey in F1. rewrite Ex in F2. injection F1 as <-. injection F2 as <-.
       rewrite (xy_some_true e b (or_intror H)) in H |- *. reflexivity.
   + rewrite G1, G2, L1, R2. exact (IL _ _ _ D1 D2 H).
Qed.

(* Shifted simulation, on values. *)
Lemma shifted_val : forall d u v b, din inC u -> din inC v ->
 E h' d (rd u) (rd v) = Some b -> E h (S d) u v = Some b.
Proof.
 induction d as [|e IHe]; [discriminate|].
 assert (IL : forall xs ys b, Forall (din inC) xs -> Forall (din inC) ys ->
   list_eq (E h' e) (map rd xs) (map rd ys) = Some b -> list_eq (E h (S e)) xs ys = Some b)
   by (apply list_unlift; exact IHe).
 induction u as [n|s|bb|t| |a1 IHa1 a2 IHa2|l1|st|x0 e0 r0|e1 r1|f0 args0|ex];
  intros v b Du Dv H; destruct v; try (cbn in H |- *; exact H).
 - cbn [rd] in H. rewrite eq_cons in H |- *. cbn in Du, Dv.
   destruct (E h' (S e) (rd a1) (rd v1)) as [[|]|] eqn:E1; try discriminate H.
   + rewrite (IHa1 _ _ (proj1 Du) (proj1 Dv) E1). exact (IHa2 _ _ (proj2 Du) (proj2 Dv) H).
   + rewrite (IHa1 _ _ (proj1 Du) (proj1 Dv) E1). exact H.
 - cbn in Du, Dv. cbn [rd] in H. rewrite eq_vec in H |- *.
   destruct (Nat.eqb_spec l1 l) as [<-|D]; [rewrite Nat.eqb_refl in H; exact H|].
   destruct (fetch l1 Du) as [A1 [A1' [F1 [G1 [D1 [L1 _]]]]]].
   destruct (fetch l Dv) as [A2 [A2' [F2 [G2 [D2 [_ R2]]]]]].
   rewrite F1, F2.
   destruct (Nat.eqb_spec (rl l1) (rl l)) as [Q|Q].
   + injection H as <-. destruct (rl_merge l1 l D Q) as [[-> ->]|[-> ->]].
     * rewrite Ex in F1. rewrite Ey in F2. injection F1 as <-. injection F2 as <-. exact (proj1 (xy_true h e)).
     * rewrite Ey in F1. rewrite Ex in F2. injection F1 as <-. injection F2 as <-. exact (proj2 (xy_true h e)).
   + rewrite G1, G2, L1, R2 in H. exact (IL _ _ _ D1 D2 H).
Qed.

Lemma same_cell : forall d p q b, In p cs -> In q cs -> rl p <> rl q ->
 cellcmp R P h d p q = Some b -> cellcmp R P h' d (rl p) (rl q) = Some b.
Proof.
 intros d p q b Ip Iq _ H. unfold cellcmp in *.
 destruct (fetch p Ip) as [A1 [A1' [F1 [G1 [D1 [L1 _]]]]]].
 destruct (fetch q Iq) as [A2 [A2' [F2 [G2 [D2 [_ R2]]]]]].
 rewrite F1, F2 in H. rewrite G1, G2, L1, R2.
 exact (list_lift _ _ _ _ (same_val d) _ _ _ D1 D2 H).
Qed.

Lemma shifted_cell : forall d p q b, In p cs -> In q cs -> rl p <> rl q ->
 cellcmp R P h' d (rl p) (rl q) = Some b -> cellcmp R P h (S d) p q = Some b.
Proof.
 intros d p q b Ip Iq _ H. unfold cellcmp in *.
 destruct (fetch p Ip) as [A1 [A1' [F1 [G1 [D1 [L1 _]]]]]].
 destruct (fetch q Iq) as [A2 [A2' [F2 [G2 [D2 [_ R2]]]]]].
 rewrite F1, F2. rewrite G1, G2, L1, R2 in H.
 exact (list_unlift _ _ _ _ (shifted_val d) _ _ _ D1 D2 H).
Qed.

Lemma xy_cell : forall d b, (cellcmp R P h d x y = Some b \/ cellcmp R P h d y x = Some b) -> b = true.
Proof. intros d b. unfold cellcmp. rewrite Ex, Ey. apply xy_some_true. Qed.

Lemma xy_cell_1 : forall d, cellcmp R P h (S d) x y = Some true /\ cellcmp R P h (S d) y x = Some true.
Proof. intro d. unfold cellcmp. rewrite Ex, Ey. apply xy_true. Qed.

Lemma rl_in : forall p, In p cs -> In (rl p) (remove Nat.eq_dec y cs).
Proof.
 intros p Ip. apply in_remove_iff. unfold JitEqBudgetStep.rl.
 destruct (Nat.eqb_spec p y); split; congruence.
Qed.

Lemma step_settled_sec : forall n,
 (forall p q, In p (remove Nat.eq_dec y cs) -> In q (remove Nat.eq_dec y cs) -> p <> q -> settled R P h' n p q) ->
 forall p q, In p cs -> In q cs -> p <> q -> settled R P h (S n) p q.
Proof.
 intros n Hs p q Ip Iq D d b H.
 destruct (Nat.eq_dec (rl p) (rl q)) as [Q|Q].
 - destruct (rl_merge p q D Q) as [[-> ->]|[-> ->]].
   + rewrite (xy_cell d b (or_introl H)). exact (proj1 (xy_cell_1 n)).
   + rewrite (xy_cell d b (or_intror H)). exact (proj2 (xy_cell_1 n)).
 - apply shifted_cell; [exact Ip|exact Iq|exact Q|].
   apply (Hs _ _ (rl_in p Ip) (rl_in q Iq) Q d). apply same_cell; assumption.
Qed.
End Sim.

(* ======================= the published statements ======================= *)
Definition num_per (P : profile) : Prop :=
 (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) /\
 (forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true).

Lemma least_agree : forall R P h cs d x y, closed_in h cs -> least_true R P h cs d x y ->
 exists X Y, nth_error h x = Some X /\ nth_error h y = Some Y /\ list_eq (leaf_eq R P) X Y = Some true.
Proof.
 intros R P h cs d x y C [Ix [Iy [_ [T Lst]]]].
 destruct (C x Ix) as [X [EX _]]. destruct (C y Iy) as [Y [EY _]]. exists X, Y.
 repeat split; auto. exact (least_true_pointers R P h cs d x y X Y C Ix Iy EX EY T Lst).
Qed.

(* (iii) *)
Theorem same_budget_sim : forall R P h cs d0 x y, num_per P -> closed_in h cs -> least_true R P h cs d0 x y ->
 forall d p q b, In p cs -> In q cs -> rl y x p <> rl y x q ->
 cellcmp R P h d p q = Some b -> cellcmp R P (surgery cs y x h) d (rl y x p) (rl y x q) = Some b.
Proof.
 intros R P h cs d0 x y [Sy Tr] C L. destruct (least_agree R P h cs d0 x y C L) as [X [Y [EX [EY Ag]]]].
 destruct L as [Ix [Iy [D _]]]. eapply same_cell; eassumption.
Qed.

(* (iv) *)
Theorem shifted_sim : forall R P h cs d0 x y, num_per P -> closed_in h cs -> least_true R P h cs d0 x y ->
 forall d p q b, In p cs -> In q cs -> rl y x p <> rl y x q ->
 cellcmp R P (surgery cs y x h) d (rl y x p) (rl y x q) = Some b -> cellcmp R P h (S d) p q = Some b.
Proof.
 intros R P h cs d0 x y [Sy Tr] C L. destruct (least_agree R P h cs d0 x y C L) as [X [Y [EX [EY Ag]]]].
 destruct L as [Ix [Iy [D _]]]. eapply shifted_cell; eassumption.
Qed.

(* The merged pair {x,y}. *)
Theorem xy_answers_true : forall R P h cs d0 x y, num_per P -> closed_in h cs -> least_true R P h cs d0 x y ->
 forall d b, (cellcmp R P h d x y = Some b \/ cellcmp R P h d y x = Some b) -> b = true.
Proof.
 intros R P h cs d0 x y [Sy Tr] C L. destruct (least_agree R P h cs d0 x y C L) as [X [Y [EX [EY Ag]]]].
 eapply xy_cell; eassumption.
Qed.

Theorem xy_true_from_1 : forall R P h cs d0 x y, num_per P -> closed_in h cs -> least_true R P h cs d0 x y ->
 forall d, cellcmp R P h (S d) x y = Some true /\ cellcmp R P h (S d) y x = Some true.
Proof.
 intros R P h cs d0 x y [Sy Tr] C L. destruct (least_agree R P h cs d0 x y C L) as [X [Y [EX [EY Ag]]]].
 eapply xy_cell_1; eassumption.
Qed.

(* The step of the induction on |cs|. *)
Theorem step_settled : forall R P h cs d0 x y n, num_per P -> closed_in h cs -> least_true R P h cs d0 x y ->
 (forall p q, In p (remove Nat.eq_dec y cs) -> In q (remove Nat.eq_dec y cs) -> p <> q ->
   settled R P (surgery cs y x h) n p q) ->
 forall p q, In p cs -> In q cs -> p <> q -> settled R P h (S n) p q.
Proof.
 intros R P h cs d0 x y n [Sy Tr] C L. destruct (least_agree R P h cs d0 x y C L) as [X [Y [EX [EY Ag]]]].
 destruct L as [Ix [Iy [D _]]]. eapply step_settled_sec; eassumption.
Qed.

(* A true pair of distinct cells gives a least one. *)
Lemma least_nat : forall (f : nat -> bool) n, f n = true -> exists m, f m = true /\ forall k, k < m -> f k = false.
Proof.
 intros f n. revert n. assert (G : forall N m, m <= N -> f m = true -> exists m, f m = true /\ forall k, k < m -> f k = false).
 { induction N as [|N IH]; intros m Lm Fm.
   - exists m. split; [exact Fm|]. intros k Lk. lia.
   - destruct (existsb f (seq 0 m)) eqn:Q.
     + apply existsb_exists in Q as [k [Ik Fk]]. apply in_seq in Ik. apply (IH k); [lia|exact Fk].
     + exists m. split; [exact Fm|]. intros k Lk.
       destruct (f k) eqn:Fk; [|reflexivity]. exfalso.
       assert (existsb f (seq 0 m) = true) by (apply existsb_exists; exists k; split; [apply in_seq; lia|exact Fk]).
       congruence. }
 intros n Fn. exact (G n n (le_n n) Fn).
Qed.

Theorem least_true_exists : forall R P h cs d p q, In p cs -> In q cs -> p <> q -> cellcmp R P h d p q = Some true ->
 exists d0 x y, least_true R P h cs d0 x y.
Proof.
 intros R P h cs d p q Ip Iq D T.
 set (tb := fun e => existsb (fun a => existsb (fun c =>
   negb (Nat.eqb a c) && match cellcmp R P h e a c with Some true => true | _ => false end) cs) cs).
 assert (Tb : forall e, tb e = true <-> exists a c, In a cs /\ In c cs /\ a <> c /\ cellcmp R P h e a c = Some true).
 { intro e. unfold tb. rewrite existsb_exists. split.
   - intros [a [Ia Q]]. apply existsb_exists in Q as [c [Ic Q]]. apply andb_true_iff in Q as [N Q].
     exists a, c. repeat split; auto.
     + intro Ac. subst. rewrite Nat.eqb_refl in N. discriminate N.
     + destruct (cellcmp R P h e a c) as [[|]|]; congruence.
   - intros [a [c [Ia [Ic [Ac Q]]]]]. exists a. split; [exact Ia|]. apply existsb_exists. exists c.
     split; [exact Ic|]. rewrite Q. apply andb_true_iff. split; [|reflexivity].
     apply negb_true_iff, Nat.eqb_neq. exact Ac. }
 destruct (least_nat tb d (proj2 (Tb d) (ex_intro _ p (ex_intro _ q (conj Ip (conj Iq (conj D T))))))) as [m [Fm Lm]].
 apply Tb in Fm as [x [y [Ix [Iy [Dxy Txy]]]]]. exists m, x, y. repeat split; auto.
 intros d' a c Ld Ia Ic Ac Q. specialize (Lm d' Ld).
 assert (tb d' = true) by (apply Tb; exists a, c; auto). congruence.
Qed.

End JitEqBudgetStep.
