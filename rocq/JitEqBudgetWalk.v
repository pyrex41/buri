(* OB-JIT-EQ-BUDGET-CORE, the base case: a walk bound on a closed set of cells with no true
   pairs. This is the "Base" paragraph of the header of rocq/JitEqBudget.v, relativized to a set S
   of cell indices. JitEqBudget.v is not edited and does not import this file.

   Statements published here (for the assembly of eq_core_statement):
   - data_ptrs v       the VVec locations that = can follow from the value v: through VCons and
                       VVec only. Closure environments and partial applications are not followed.
   - closed_in h S     every location in the data of a cell of S is in S.
   - no_true_pairs R P h S
                       no two distinct p, q in S have cellcmp R P h d p q = Some true, for any d.
   - walk_bound_pred : forall R P h S, num_cmp P PEqual symmetric -> transitive ->
       closed_in h S -> no_true_pairs R P h S ->
       forall d p q b, p <> q -> In p S -> In q S -> cellcmp R P h d p q = Some b ->
       cellcmp R P h (pred (length S)) p q = Some b.
   - walk_bound      : the same hypotheses and premises, conclusion
       cellcmp R P h (length S) p q = Some b.
   - walk_bound_needs_trans : walk_bound without the transitivity hypothesis is false
       (JitEqBudget's tolerance profile `tol` and heap h5).

   The hypotheses mention no lok at all, neither global nor S-local: the proof does not need one.
   It does not need NoDup S, nor that S lies below length h, either; a caller that has these
   simply does not pass them. Every theorem here is closed under the global context (Audit_Jit).

   ---- The argument ----
   A cell's contents are flattened into a token stream: a VCons gives TCons followed by its two
   parts, any other value gives TLeaf of itself, and the cell ends with TEnd (`ctoks`). Streams
   are padded with TEnd. Comparing two tokens (`tev`) gives
   - EAgree: TCons with TCons, TEnd with TEnd, two leaves that = takes as equal without reading
     the heap (number equality under P, symbol and string equality, closure ids, and pointer
     identity for VVec),
   - EPtr a b: VVec a against VVec b with a <> b,
   - EStop r: anything else, with = 's answer r (never Some true).
   Agreement is a PER (leaf_agree_sym, leaf_agree_trans): this is where the two hypotheses on
   number equality are used. A VVec agrees only with itself (agree_vec).

   `link_cell`: when no pointer pair met answers true, = on two cells at budget S d is decided by
   the first index at which their streams disagree (`fstop`): EStop r answers r, EPtr a b answers
   cellcmp d a b. So a comparison with a Some answer is a walk e_0, ..., e_L of cell pairs, each
   e_(i+1) the pointer pair at which e_i stops, the last stopping at an EStop (`walk_of_answer`),
   and cellcmp (L + 1) e_0 already gives the answer.

   pos(e) is the list of stop indices along the walk from e. The order on these lists is
   lexicographic with a prefix below its extensions (`ltl`). `gt t u v` says pos(u,v) > t, and
   is defined for every t without pos: the streams of u and v agree before index k, and at k
   they agree or hold VVec a and VVec b with gt t' a b, where t = k :: t'. gt t is symmetric and
   transitive (the ultrametric lemma, from the PER), so `E t u v := u = v \/ gt t u v` is an
   equivalence on cell indices (the threshold equivalence), and it gets finer as t grows
   (E_mono). For e_i = (u, v): E pos(e_i) separates u and v, and every E t with t < pos(e_i)
   joins them (walk_witness). The pos(e_i) are distinct (their lengths differ). Taking them in
   increasing order, each refines the partition of S strictly (ncls_strict), and the coarsest
   has at least two classes, so L + 2 <= |S| (count_thresholds). Hence cellcmp (|S| - 1) e_0
   gives the answer, one better than |S|. *)
From Coq Require Import List Arith NArith Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitEqBudget.
Import ListNotations.
Module JitEqBudgetWalk.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 KLPort.KLPort JitEqBudget.JitEqBudget.
Local Open Scope nat_scope.

(* ======================= the published hypotheses ======================= *)
Fixpoint data_ptrs (v : value) : list nat := match v with
 | VCons a b => data_ptrs a ++ data_ptrs b
 | VVec l => [l]
 | _ => [] end.

Definition closed_in (h : list (list value)) (S : list nat) : Prop :=
 forall p xs, In p S -> nth_error h p = Some xs -> forall l, In l (flat_map data_ptrs xs) -> In l S.

Definition no_true_pairs (R : port_rules) (P : profile) (h : list (list value)) (S : list nat) : Prop :=
 forall d p q, In p S -> In q S -> p <> q -> cellcmp R P h d p q <> Some true.

Lemma cellcmp_mono : forall R P h d d' p q y, d <= d' ->
 cellcmp R P h d p q = Some y -> cellcmp R P h d' p q = Some y.
Proof.
 intros R P h d d' p q y L. unfold cellcmp.
 destruct (nth_error h p), (nth_error h q); try discriminate.
 apply list_eq_mono. intros u v z. apply eq_depth_mono_le. exact L.
Qed.

(* ======================= lexicographic order on stop paths ======================= *)
Fixpoint ltl (t t' : list nat) : bool := match t, t' with
 | [], [] => false
 | [], _ :: _ => true
 | _ :: _, [] => false
 | k :: s, k' :: s' => (k <? k') || ((k =? k') && ltl s s') end.

Lemma ltl_irrefl : forall t, ltl t t = false.
Proof.
 induction t as [|k t IH]; cbn [ltl]; [reflexivity|]. rewrite Nat.ltb_irrefl, Nat.eqb_refl, IH. reflexivity.
Qed.

Lemma ltl_cons : forall k s k' s', ltl (k :: s) (k' :: s') = true <->
 k < k' \/ (k = k' /\ ltl s s' = true).
Proof.
 intros. cbn [ltl]. rewrite orb_true_iff, andb_true_iff, Nat.ltb_lt, Nat.eqb_eq. reflexivity.
Qed.

Lemma ltl_trans : forall t1 t2 t3, ltl t1 t2 = true -> ltl t2 t3 = true -> ltl t1 t3 = true.
Proof.
 induction t1 as [|k1 s1 IH]; intros [|k2 s2] [|k3 s3]; try (cbn; congruence).
 rewrite !ltl_cons. intros [A|[-> A]] [B|[-> B]]; [left; lia|left; lia|left; lia|].
 right. split; [reflexivity|]. exact (IH _ _ A B).
Qed.

Lemma ltl_total : forall t t', t <> t' -> ltl t t' = true \/ ltl t' t = true.
Proof.
 induction t as [|k s IH]; intros [|k' s'] D; [congruence|left; reflexivity|right; reflexivity|].
 rewrite !ltl_cons.
 destruct (Nat.lt_trichotomy k k') as [L|[<-|L]]; auto.
 assert (s <> s') by congruence. destruct (IH s' H); auto.
Qed.

Lemma ltl_nil_l : forall t, t <> [] -> ltl [] t = true.
Proof. intros [|k s] H; [congruence|reflexivity]. Qed.

Fixpoint maxl (T : list (list nat)) : list nat := match T with
 | [] => []
 | t :: T' => if ltl (maxl T') t then t else maxl T' end.

Lemma maxl_ge : forall T t, In t T -> t = maxl T \/ ltl t (maxl T) = true.
Proof.
 induction T as [|t0 T IH]; intros t I; [destruct I|]. cbn.
 destruct (ltl (maxl T) t0) eqn:L; destruct I as [<-|I].
 - left; reflexivity.
 - right. destruct (IH t I) as [->|A]; [exact L|exact (ltl_trans _ _ _ A L)].
 - destruct (list_eq_dec Nat.eq_dec t0 (maxl T)) as [E|D]; [left; exact E|].
   destruct (ltl_total _ _ D) as [A|A]; [right; exact A|congruence].
 - exact (IH t I).
Qed.

Lemma maxl_in : forall T, T <> [] -> In (maxl T) T.
Proof.
 induction T as [|t0 T IH]; intro H; [congruence|]. cbn.
 destruct (ltl (maxl T) t0) eqn:L; [left; reflexivity|].
 destruct T as [|t1 T'].
 - cbn in L |- *. destruct t0 as [|k s]; [left; reflexivity|discriminate].
 - right. apply IH. discriminate.
Qed.

(* ======================= counting classes ======================= *)
(* The number of classes of a decidable relation on a list: an element counts when no earlier
   element is related to it. *)
Fixpoint ncls_aux (e : nat -> nat -> bool) (seen xs : list nat) : nat := match xs with
 | [] => 0
 | x :: xs' => (if existsb (fun s => e s x) seen then 0 else 1) + ncls_aux e (x :: seen) xs' end.

Lemma ncls_le : forall e xs seen, ncls_aux e seen xs <= length xs.
Proof.
 intro e. induction xs as [|x xs IH]; intro seen; cbn; [lia|].
 specialize (IH (x :: seen)). destruct (existsb _ seen); lia.
Qed.

Lemma ncls_pos : forall e x xs, 1 <= ncls_aux e [] (x :: xs).
Proof. intros. cbn. lia. Qed.

Section Count.
Variables e e' : nat -> nat -> bool.
Hypothesis Hsub : forall a b, e' a b = true -> e a b = true.

Lemma existsb_sub : forall seen x, existsb (fun s => e' s x) seen = true -> existsb (fun s => e s x) seen = true.
Proof.
 intros seen x H. apply existsb_exists in H as [s [I H]]. apply existsb_exists. exists s. auto.
Qed.

Lemma ncls_mono : forall xs seen, ncls_aux e seen xs <= ncls_aux e' seen xs.
Proof.
 induction xs as [|x xs IH]; intro seen; cbn; [lia|]. specialize (IH (x :: seen)).
 destruct (existsb (fun s => e' s x) seen) eqn:A.
 - rewrite (existsb_sub _ _ A). lia.
 - destruct (existsb (fun s => e s x) seen); lia.
Qed.

Hypotheses (Esym : forall a b, e a b = true -> e b a = true)
 (Etr : forall a b c, e a b = true -> e b c = true -> e a c = true)
 (Erefl' : forall a, e' a a = true) (Esym' : forall a b, e' a b = true -> e' b a = true)
 (Etr' : forall a b c, e' a b = true -> e' b c = true -> e' a c = true).

Definition faithful (l : list nat) : Prop := forall a b, In a l -> In b l -> e a b = true -> e' a b = true.

Lemma faithful_cons : forall seen x, faithful seen ->
 (existsb (fun s => e s x) seen = true -> existsb (fun s => e' s x) seen = true) ->
 faithful (x :: seen).
Proof.
 intros seen x F Hx.
 assert (One : forall a, In a seen -> e a x = true -> e' a x = true).
 { intros a I H. assert (A : existsb (fun s => e s x) seen = true)
     by (apply existsb_exists; exists a; auto).
   apply Hx, existsb_exists in A as [s [Is Hs]].
   assert (e a s = true) by exact (Etr _ _ _ H (Esym _ _ (Hsub _ _ Hs))).
   exact (Etr' _ _ _ (F _ _ I Is H0) Hs). }
 intros a b [<-|Ia] [<-|Ib] H.
 - apply Erefl'.
 - apply Esym', One; [exact Ib|exact (Esym _ _ H)].
 - apply One; assumption.
 - apply F; assumption.
Qed.

Lemma ncls_faithful : forall xs seen, faithful seen -> ncls_aux e seen xs = ncls_aux e' seen xs ->
 faithful (seen ++ xs).
Proof.
 induction xs as [|x xs IH]; intros seen F Q; [rewrite app_nil_r; exact F|].
 cbn in Q. pose proof (ncls_mono xs (x :: seen)) as M.
 assert (Step : existsb (fun s => e s x) seen = true -> existsb (fun s => e' s x) seen = true).
 { intro A. rewrite A in Q. destruct (existsb (fun s => e' s x) seen); [reflexivity|lia]. }
 assert (Q' : ncls_aux e (x :: seen) xs = ncls_aux e' (x :: seen) xs).
 { destruct (existsb (fun s => e' s x) seen) eqn:A'.
   - rewrite (existsb_sub _ _ A') in Q. lia.
   - destruct (existsb (fun s => e s x) seen) eqn:A; [discriminate (Step eq_refl)|lia]. }
 pose proof (IH _ (faithful_cons _ _ F Step) Q') as G.
 intros a b Ia Ib. apply G; rewrite in_app_iff in *; cbn in *; tauto.
Qed.

Lemma ncls_strict : forall S x y, In x S -> In y S -> e x y = true -> e' x y = false ->
 ncls_aux e [] S < ncls_aux e' [] S.
Proof.
 intros S x y Ix Iy E E'. pose proof (ncls_mono S []) as M.
 destruct (Nat.eq_dec (ncls_aux e [] S) (ncls_aux e' [] S)) as [Q|D]; [|lia].
 assert (F : faithful []) by (intros a b []).
 pose proof (ncls_faithful S [] F Q x y Ix Iy E). congruence.
Qed.
End Count.

(* ======================= tokens ======================= *)
Inductive tok := TCons | TEnd | TLeaf (v : value).

Fixpoint vtoks (v : value) : list tok := match v with
 | VCons a b => TCons :: vtoks a ++ vtoks b
 | _ => [TLeaf v] end.
Definition ctoks (xs : list value) : list tok := flat_map vtoks xs ++ [TEnd].
Definition tk (s : list tok) (i : nat) : tok := nth i s TEnd.

Inductive ev := EAgree | EStop (r : option bool) | EPtr (a b : nat).

Section Walk.
Variables (R : port_rules) (P : profile) (h : list (list value)).

(* What = answers on two leaves when it reads no heap. *)
Definition leafr (a b : value) : option bool := eq_depth_r R P [] 1 a b.

Definition lev (a b : value) : ev := match a, b with
 | VCons _ _, _ | _, VCons _ _ => EStop (Some false)
 | VVec l1, VVec l2 => if Nat.eqb l1 l2 then EAgree else EPtr l1 l2
 | _, _ => match leafr a b with Some true => EAgree | r => EStop r end end.

Definition tev (x y : tok) : ev := match x, y with
 | TCons, TCons => EAgree
 | TEnd, TEnd => EAgree
 | TLeaf a, TLeaf b => lev a b
 | _, _ => EStop (Some false) end.

Definition agreeb (x y : tok) : bool := match tev x y with EAgree => true | _ => false end.

Definition ctk (u : nat) : list tok := match nth_error h u with Some xs => ctoks xs | None => [] end.

(* ---------- agreement is a PER ---------- *)
Definition lag (a b : value) : Prop := match a, b with
 | VNum x, VNum y => num_cmp P PEqual x y = true
 | VSym x, VSym y | VStr x, VStr y => x = y
 | VBool x, VBool y => x = y
 | VNil, VNil => True
 | VStream x, VStream y => x = y
 | VVec x, VVec y => x = y
 | VLam _ _ r1, VLam _ _ r2 | VFrozen _ r1, VFrozen _ r2 =>
   object_identity R = true /\ exists i, closure_id r1 = Some i /\ closure_id r2 = Some i
 | _, _ => False end.

Lemma lev_agree : forall a b, lev a b = EAgree <-> lag a b.
Proof.
 intros a b. destruct a, b; cbn [lev lag leafr eq_depth_r]; try (split; [discriminate|contradiction]);
  try (split; [intros _; exact I|reflexivity]); unfold eq_opaque_r, opaque_eq.
 all: try (match goal with |- context [object_identity R] => idtac end;
   destruct (object_identity R); cbn; split; intro HH; try discriminate; try contradiction; fail).
 all: try (match goal with |- context [closure_id ?r] => idtac end;
   destruct (object_identity R); cbn;
   repeat match goal with |- context [closure_id ?r] => destruct (closure_id r) end; cbn;
   try match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y) as [<-|?] end;
   (split; [intro HH; first [discriminate | split; [reflexivity|eauto]] | intros [HO [i [A B]]]; congruence])).
 - destruct (num_cmp P PEqual n n0); split; congruence.
 - destruct (text_eqb s s0) eqn:E; [apply text_eqb_eq in E; subst; split; auto|].
   apply text_eqb_neq in E. split; [discriminate|contradiction].
 - destruct b, b0; cbn; split; congruence.
 - destruct (text_eqb t t0) eqn:E; [apply text_eqb_eq in E; subst; split; auto|].
   apply text_eqb_neq in E. split; [discriminate|contradiction].
 - destruct (Nat.eqb_spec l l0); split; congruence.
 - destruct (N.eqb_spec h0 h1); split; congruence.
Qed.

Hypotheses (Hsym : forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x)
 (Htr : forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true).

Lemma lag_sym : forall a b, lag a b -> lag b a.
Proof.
 intros a b. destruct a, b; cbn; try contradiction; try (intros; subst; auto; fail).
 - rewrite Hsym. auto.
 - intros [O [i [A B]]]. eauto.
 - intros [O [i [A B]]]. eauto.
Qed.

Lemma lag_trans : forall a b c, lag a b -> lag b c -> lag a c.
Proof.
 intros a b c. destruct a, b; cbn; try contradiction; destruct c; cbn; try contradiction;
  try (intros; subst; auto; fail).
 - apply Htr.
 - intros [O [i [A B]]] [_ [j [C D]]]. rewrite B in C. injection C as <-. eauto.
 - intros [O [i [A B]]] [_ [j [C D]]]. rewrite B in C. injection C as <-. eauto.
Qed.

Lemma agree_leaf : forall a b, agreeb (TLeaf a) (TLeaf b) = true <-> lag a b.
Proof.
 intros a b. unfold agreeb. cbn [tev]. rewrite <- lev_agree.
 destruct (lev a b); split; congruence.
Qed.

Lemma agree_sym : forall x y, agreeb x y = true -> agreeb y x = true.
Proof.
 intros [| |a] [| |b]; try (cbn; congruence). rewrite !agree_leaf. apply lag_sym.
Qed.

Lemma agree_trans : forall x y z, agreeb x y = true -> agreeb y z = true -> agreeb x z = true.
Proof.
 intros [| |a] [| |b] [| |c]; try (cbn; congruence). rewrite !agree_leaf. apply lag_trans.
Qed.

Lemma agree_vec : forall x l, agreeb x (TLeaf (VVec l)) = true -> x = TLeaf (VVec l).
Proof.
 intros [| |a] l; try (cbn; congruence). rewrite agree_leaf.
 destruct a; cbn; try contradiction. intros ->. reflexivity.
Qed.

Lemma tev_ptr : forall x y a b, tev x y = EPtr a b -> x = TLeaf (VVec a) /\ y = TLeaf (VVec b) /\ a <> b.
Proof.
 intros [| |u] [| |w] a b; cbn [tev]; try discriminate.
 destruct (match u, w with VVec _, VVec _ => true | _, _ => false end) eqn:V.
 - destruct u; try discriminate V; destruct w; try discriminate V. cbn [lev].
   destruct (Nat.eqb_spec l l0); [discriminate|]. intro H. injection H as <- <-. auto.
 - intro H. exfalso. destruct u, w; try discriminate V; cbn [lev] in H; try discriminate H;
    destruct (leafr _ _) as [[|]|]; discriminate H.
Qed.

Lemma tev_vec : forall a b, tev (TLeaf (VVec a)) (TLeaf (VVec b)) = if Nat.eqb a b then EAgree else EPtr a b.
Proof. reflexivity. Qed.

(* ---------- the first disagreement ---------- *)
Definition shift (o : option (nat * ev)) : option (nat * ev) :=
 match o with Some (j, e) => Some (S j, e) | None => None end.

Fixpoint fstopR (s : list tok) : option (nat * ev) := match s with
 | [] => None
 | t :: s' => match tev TEnd t with EAgree => shift (fstopR s') | e => Some (0, e) end end.

Fixpoint fstop (s1 s2 : list tok) : option (nat * ev) := match s1 with
 | [] => fstopR s2
 | t1 :: s1' => match tev t1 (hd TEnd s2) with EAgree => shift (fstop s1' (tl s2)) | e => Some (0, e) end end.

Definition stop_spec (s1 s2 : list tok) (o : option (nat * ev)) : Prop := match o with
 | None => forall i, agreeb (tk s1 i) (tk s2 i) = true
 | Some (j, e) => (forall i, i < j -> agreeb (tk s1 i) (tk s2 i) = true) /\
     tev (tk s1 j) (tk s2 j) = e /\ e <> EAgree end.

Lemma tk_nil : forall i, tk [] i = TEnd.
Proof. intros [|i]; reflexivity. Qed.
Lemma tk_tl : forall s i, tk s (S i) = tk (tl s) i.
Proof. intros [|t s] i; [rewrite !tk_nil; reflexivity|reflexivity]. Qed.
Lemma tk_hd : forall s, tk s 0 = hd TEnd s.
Proof. intros [|t s]; reflexivity. Qed.

Lemma stop_spec_cons : forall s1 s2 t1 t2,
 tk s1 0 = t1 -> tk s2 0 = t2 ->
 forall o, stop_spec (tl s1) (tl s2) o ->
 stop_spec s1 s2 (match tev t1 t2 with EAgree => shift o | e => Some (0, e) end).
Proof.
 intros s1 s2 t1 t2 H1 H2 o Ho. destruct (tev t1 t2) eqn:T.
 - destruct o as [[j e]|]; cbn in Ho |- *.
   + destruct Ho as [A [B C]]. split; [|rewrite !tk_tl; auto].
     intros [|i] L; [unfold agreeb; rewrite H1, H2, T; reflexivity|].
     rewrite !tk_tl. apply A. lia.
   + intros [|i]; [unfold agreeb; rewrite H1, H2, T; reflexivity|]. rewrite !tk_tl. apply Ho.
 - cbn. split; [intros; lia|]. rewrite H1, H2, T. split; [reflexivity|discriminate].
 - cbn. split; [intros; lia|]. rewrite H1, H2, T. split; [reflexivity|discriminate].
Qed.

Lemma fstopR_spec : forall s, stop_spec [] s (fstopR s).
Proof.
 induction s as [|t s IH].
 - intro i. rewrite !tk_nil. reflexivity.
 - cbn [fstopR]. apply (stop_spec_cons [] (t :: s) TEnd t); [apply tk_nil|reflexivity|exact IH].
Qed.

Lemma fstop_spec : forall s1 s2, stop_spec s1 s2 (fstop s1 s2).
Proof.
 induction s1 as [|t1 s1 IH]; intro s2; [apply fstopR_spec|].
 cbn [fstop]. apply (stop_spec_cons (t1 :: s1) s2 t1 (hd TEnd s2));
  [reflexivity|apply tk_hd|exact (IH (tl s2))].
Qed.

(* ---------- = on two cells is decided at the first disagreement ---------- *)
Definition res (d : nat) (e : ev) : option bool := match e with
 | EAgree => Some true
 | EStop r => r
 | EPtr a b => cellcmp R P h d a b end.
Definition resk (d : nat) (o : option (nat * ev)) : option bool := match o with
 | None => Some true
 | Some (_, e) => res d e end.

Lemma resk_cons : forall d t1 s1 t2 s2, resk d (fstop (t1 :: s1) (t2 :: s2)) =
 match tev t1 t2 with EAgree => resk d (fstop s1 s2) | e => res d e end.
Proof.
 intros. cbn [fstop hd tl]. destruct (tev t1 t2); try reflexivity.
 destruct (fstop s1 s2) as [[j e]|]; reflexivity.
Qed.

Definition NT (d : nat) (A B : list nat) : Prop :=
 forall l1 l2, In l1 A -> In l2 B -> l1 <> l2 -> cellcmp R P h d l1 l2 <> Some true.

Lemma NT_app_l : forall d A1 A2 B, NT d (A1 ++ A2) B -> NT d A1 B /\ NT d A2 B.
Proof. intros d A1 A2 B H. split; intros l1 l2 I1 I2; apply H; auto; apply in_app_iff; auto. Qed.
Lemma NT_app_r : forall d A B1 B2, NT d A (B1 ++ B2) -> NT d A B1 /\ NT d A B2.
Proof. intros d A B1 B2 H. split; intros l1 l2 I1 I2; apply H; auto; apply in_app_iff; auto. Qed.

Definition notcons (v : value) : Prop := match v with VCons _ _ => False | _ => True end.

Lemma vtoks_leaf : forall v, notcons v -> vtoks v = [TLeaf v].
Proof. intros [] H; cbn in H; tauto || reflexivity. Qed.

Lemma eq_leaf : forall d a b, notcons a -> notcons b ->
 (forall l1 l2, a = VVec l1 -> b = VVec l2 -> False) ->
 eq_depth_r R P h (S d) a b = leafr a b /\ lev a b = match leafr a b with Some true => EAgree | r => EStop r end.
Proof.
 intros d a b Ha Hb V. destruct a, b; cbn in Ha, Hb; try contradiction;
  try (exfalso; eapply V; reflexivity); split; reflexivity.
Qed.

Lemma link_leaf : forall d a b s1 s2, notcons a -> notcons b -> NT d (data_ptrs a) (data_ptrs b) ->
 resk d (fstop (TLeaf a :: s1) (TLeaf b :: s2)) =
 match eq_depth_r R P h (S d) a b with Some true => resk d (fstop s1 s2) | r => r end.
Proof.
 intros d a b s1 s2 Ha Hb N. rewrite resk_cons. cbn [tev].
 destruct (match a with VVec l => Some l | _ => None end) as [l1|] eqn:A1;
 destruct (match b with VVec l => Some l | _ => None end) as [l2|] eqn:B1.
 1: { destruct a; try discriminate. destruct b; try discriminate. injection A1 as ->. injection B1 as ->.
   cbn [lev]. change (eq_depth_r R P h (S d) (VVec l1) (VVec l2)) with
     (if Nat.eqb l1 l2 then Some true else cellcmp R P h d l1 l2).
   destruct (Nat.eqb_spec l1 l2) as [_|D]; [reflexivity|]. cbn [res].
   specialize (N l1 l2 (or_introl eq_refl) (or_introl eq_refl) D).
   destruct (cellcmp R P h d l1 l2) as [[|]|]; congruence. }
 all: assert (V : forall l1 l2, a = VVec l1 -> b = VVec l2 -> False)
     by (intros ? ? -> ->; discriminate).
 all: destruct (eq_leaf d a b Ha Hb V) as [E L]; rewrite E, L.
 all: destruct (leafr a b) as [[|]|]; reflexivity.
Qed.

Lemma link_v : forall d a b s1 s2, NT d (data_ptrs a) (data_ptrs b) ->
 resk d (fstop (vtoks a ++ s1) (vtoks b ++ s2)) =
 match eq_depth_r R P h (S d) a b with Some true => resk d (fstop s1 s2) | r => r end.
Proof.
 intro d. induction a as [n|s|bb|t| |a1 IH1 a2 IH2|l|st|x0 e0 r0|e1 r1|f0 args0|ex]; intros w s1 s2 N.
 6: { destruct w as [n'|s'|bb'|t'| |b1 b2|l'|st'|x1 e2 r2|e3 r3|f1 args1|ex'].
   6: { cbn [vtoks data_ptrs app] in N |- *. rewrite <- !app_assoc, resk_cons. cbn [tev].
     apply NT_app_l in N as [N1 N2]. apply NT_app_r in N1 as [N11 _]. apply NT_app_r in N2 as [_ N22].
     rewrite (IH1 b1 _ _ N11).
     change (eq_depth_r R P h (S d) (VCons a1 a2) (VCons b1 b2)) with
       (match eq_depth_r R P h (S d) a1 b1 with Some true => eq_depth_r R P h (S d) a2 b2 | r => r end).
     destruct (eq_depth_r R P h (S d) a1 b1) as [[|]|]; try reflexivity.
     rewrite (IH2 b2 _ _ N22). reflexivity. }
   all: cbn [vtoks app]; rewrite resk_cons; reflexivity. }
 all: destruct (match w with VCons _ _ => true | _ => false end) eqn:Wc.
 all: try (destruct w; try discriminate Wc; cbn [vtoks app]; rewrite resk_cons; reflexivity; fail).
 all: rewrite (vtoks_leaf w) by (destruct w; try discriminate Wc; exact I); cbn [vtoks app].
 all: apply link_leaf; [exact I|destruct w; try discriminate Wc; exact I|exact N].
Qed.

Lemma vtoks_head : forall v, exists t r, vtoks v = t :: r /\ tev TEnd t = EStop (Some false)
 /\ tev t TEnd = EStop (Some false).
Proof. intros []; cbn; eexists _, _; repeat split. Qed.

Lemma link_c : forall d xs ys, NT d (flat_map data_ptrs xs) (flat_map data_ptrs ys) ->
 resk d (fstop (ctoks xs) (ctoks ys)) = list_eq (eq_depth_r R P h (S d)) xs ys.
Proof.
 intro d. unfold ctoks. induction xs as [|x xs IH]; intros [|y ys] N.
 - reflexivity.
 - cbn [flat_map]. destruct (vtoks_head y) as [t [r [V [A _]]]]. rewrite <- app_assoc, V.
   cbn [app]. rewrite resk_cons, A. reflexivity.
 - cbn [flat_map]. destruct (vtoks_head x) as [t [r [V [_ A]]]]. rewrite <- app_assoc, V.
   cbn [app]. rewrite resk_cons, A. reflexivity.
 - cbn [flat_map list_eq] in N |- *. rewrite <- !app_assoc.
   apply NT_app_l in N as [N1 N2]. apply NT_app_r in N1 as [N11 _]. apply NT_app_r in N2 as [_ N22].
   rewrite (link_v d x y _ _ N11).
   destruct (eq_depth_r R P h (S d) x y) as [[|]|]; try reflexivity. exact (IH ys N22).
Qed.

Lemma link_cell : forall d u v xs ys, nth_error h u = Some xs -> nth_error h v = Some ys ->
 NT d (flat_map data_ptrs xs) (flat_map data_ptrs ys) ->
 cellcmp R P h (S d) u v = resk d (fstop (ctk u) (ctk v)).
Proof.
 intros d u v xs ys Hu Hv N. unfold cellcmp, ctk. rewrite Hu, Hv. symmetry. exact (link_c d xs ys N).
Qed.

(* ---------- pointers met in a stream come from the data ---------- *)
Lemma tk_in : forall s k v, tk s k = TLeaf v -> In (TLeaf v) s.
Proof.
 intros s k v H. unfold tk in H. destruct (nth_in_or_default k s TEnd) as [I|D].
 - rewrite H in I. exact I.
 - rewrite D in H. discriminate.
Qed.

Lemma vtoks_ptr : forall v l, In (TLeaf (VVec l)) (vtoks v) -> In l (data_ptrs v).
Proof.
 induction v; cbn; intros l' I; try (destruct I as [I|[]]; discriminate I).
 - destruct I as [I|I]; [discriminate I|]. apply in_app_iff in I as [I|I]; apply in_app_iff; auto.
 - destruct I as [I|[]]. injection I as ->. auto.
Qed.

Lemma ctoks_ptr : forall xs l, In (TLeaf (VVec l)) (ctoks xs) -> In l (flat_map data_ptrs xs).
Proof.
 intros xs l I. unfold ctoks in I. apply in_app_iff in I as [I|[I|[]]]; [|discriminate I].
 apply in_flat_map in I as [x [Ix I]]. apply in_flat_map. exists x. split; [exact Ix|].
 exact (vtoks_ptr x l I).
Qed.

(* ======================= the walk ======================= *)
Variable Sc : list nat.
Hypotheses (Hclosed : closed_in h Sc) (Hnt : no_true_pairs R P h Sc).

Lemma NT_of : forall d u v xs ys, In u Sc -> In v Sc -> nth_error h u = Some xs -> nth_error h v = Some ys ->
 NT d (flat_map data_ptrs xs) (flat_map data_ptrs ys).
Proof.
 intros d u v xs ys Iu Iv Hu Hv l1 l2 I1 I2 D. apply Hnt; [exact (Hclosed u xs Iu Hu l1 I1)|exact (Hclosed v ys Iv Hv l2 I2)|exact D].
Qed.

Lemma ptr_in_S : forall u xs k a, In u Sc -> nth_error h u = Some xs -> tk (ctk u) k = TLeaf (VVec a) -> In a Sc.
Proof.
 intros u xs k a Iu Hu T. apply (Hclosed u xs Iu Hu). apply ctoks_ptr.
 unfold ctk in T. rewrite Hu in T. exact (tk_in _ _ _ T).
Qed.

Inductive walk : list (nat * nat) -> Prop :=
 | w_end u v k r : u <> v -> In u Sc -> In v Sc ->
     fstop (ctk u) (ctk v) = Some (k, EStop r) -> walk [(u, v)]
 | w_step u v k a b W : u <> v -> In u Sc -> In v Sc ->
     fstop (ctk u) (ctk v) = Some (k, EPtr a b) -> walk ((a, b) :: W) -> walk ((u, v) :: (a, b) :: W).

Lemma cellcmp_some_cells : forall d u v y, cellcmp R P h d u v = Some y ->
 exists xs ys, nth_error h u = Some xs /\ nth_error h v = Some ys.
Proof.
 intros d u v y H. unfold cellcmp in H. destruct (nth_error h u), (nth_error h v); try discriminate. eauto.
Qed.

Theorem walk_of_answer : forall d u v b, u <> v -> In u Sc -> In v Sc -> cellcmp R P h d u v = Some b ->
 exists W, walk ((u, v) :: W) /\ cellcmp R P h (S (length W)) u v = Some b.
Proof.
 induction d as [|d IH]; intros u v b D Iu Iv H;
  destruct (cellcmp_some_cells _ _ _ _ H) as [xs [ys [Hu Hv]]].
 - (* budget 0: only a difference in length answers *)
   pose proof H as H0. unfold cellcmp in H0. rewrite Hu, Hv in H0.
   assert (Hf : fstop (ctk u) (ctk v) = Some (0, EStop (Some false)) /\ b = false).
   { unfold ctk, ctoks. rewrite Hu, Hv.
     destruct xs as [|x xs], ys as [|y ys]; cbn [list_eq] in H0.
     - exfalso. apply (Hnt 0 u v Iu Iv D). rewrite H. congruence.
     - injection H0 as <-. destruct (vtoks_head y) as [t [r [V [A _]]]]. cbn [flat_map].
       rewrite <- app_assoc, V. cbn [app fstop hd tl]. rewrite A. split; reflexivity.
     - injection H0 as <-. destruct (vtoks_head x) as [t [r [V [_ A]]]]. cbn [flat_map].
       rewrite <- app_assoc, V. cbn [app fstop hd tl]. rewrite A. split; reflexivity.
     - discriminate H0. }
   destruct Hf as [Hf ->]. exists []. split; [exact (w_end u v 0 (Some false) D Iu Iv Hf)|].
   apply (cellcmp_mono R P h 0 1); [lia|exact H].
 - rewrite (link_cell d u v xs ys Hu Hv (NT_of d u v xs ys Iu Iv Hu Hv)) in H.
   pose proof (fstop_spec (ctk u) (ctk v)) as Sp.
   destruct (fstop (ctk u) (ctk v)) as [[k [|r|a b']]|] eqn:F; cbn in H, Sp.
   + exfalso. destruct Sp as [_ [_ C]]. exact (C eq_refl).
   + subst r. exists []. split; [exact (w_end u v k (Some b) D Iu Iv F)|].
     cbn [length]. rewrite (link_cell 0 u v xs ys Hu Hv (NT_of 0 u v xs ys Iu Iv Hu Hv)), F. reflexivity.
   + destruct Sp as [_ [T _]]. apply tev_ptr in T as [Ta [Tb Dab]].
     pose proof (ptr_in_S u xs k a Iu Hu Ta) as Ia. pose proof (ptr_in_S v ys k b' Iv Hv Tb) as Ib.
     destruct (IH a b' b Dab Ia Ib H) as [W [Hw Hc]].
     exists ((a, b') :: W). split; [exact (w_step u v k a b' W D Iu Iv F Hw)|].
     cbn [length]. rewrite (link_cell (S (length W)) u v xs ys Hu Hv (NT_of _ u v xs ys Iu Iv Hu Hv)), F.
     exact Hc.
   + exfalso. apply (Hnt (S d) u v Iu Iv D).
     rewrite (link_cell d u v xs ys Hu Hv (NT_of d u v xs ys Iu Iv Hu Hv)), F. reflexivity.
Qed.

(* ======================= the threshold equivalence ======================= *)
Definition agree_upto (s1 s2 : list tok) (k : nat) : bool :=
 forallb (fun i => agreeb (tk s1 i) (tk s2 i)) (seq 0 k).

Lemma agree_upto_iff : forall s1 s2 k, agree_upto s1 s2 k = true <->
 forall i, i < k -> agreeb (tk s1 i) (tk s2 i) = true.
Proof.
 intros. unfold agree_upto. rewrite forallb_forall. split; intros H i L.
 - apply H. apply in_seq. lia.
 - apply in_seq in L. apply H. lia.
Qed.

Definition ptrb (g : nat -> nat -> bool) (x y : tok) : bool := match x, y with
 | TLeaf (VVec a), TLeaf (VVec b) => g a b
 | _, _ => false end.

Fixpoint gt (t : list nat) (u v : nat) {struct t} : bool := match t with
 | [] => true
 | k :: t' => agree_upto (ctk u) (ctk v) k &&
     (agreeb (tk (ctk u) k) (tk (ctk v) k) || ptrb (gt t') (tk (ctk u) k) (tk (ctk v) k)) end.

Definition E (t : list nat) (u v : nat) : bool := Nat.eqb u v || gt t u v.

Lemma gt_cons : forall k t u v, gt (k :: t) u v = true <->
 (forall i, i < k -> agreeb (tk (ctk u) i) (tk (ctk v) i) = true) /\
 (agreeb (tk (ctk u) k) (tk (ctk v) k) = true \/ ptrb (gt t) (tk (ctk u) k) (tk (ctk v) k) = true).
Proof. intros. cbn [gt]. rewrite andb_true_iff, orb_true_iff, agree_upto_iff. reflexivity. Qed.

Lemma ptrb_sym : forall g x y, (forall a b, g a b = true -> g b a = true) ->
 ptrb g x y = true -> ptrb g y x = true.
Proof. intros g [| |[]] [| |[]]; cbn; try discriminate; auto. Qed.

Lemma gt_sym : forall t u v, gt t u v = true -> gt t v u = true.
Proof.
 induction t as [|k t IH]; intros u v; [reflexivity|]. rewrite !gt_cons.
 intros [A B]. split; [intros i L; apply agree_sym, A, L|].
 destruct B as [B|B]; [left; apply agree_sym, B|right; exact (ptrb_sym _ _ _ IH B)].
Qed.

Lemma ptrb_shape : forall g x y, ptrb g x y = true -> exists a b, x = TLeaf (VVec a) /\ y = TLeaf (VVec b) /\ g a b = true.
Proof. intros g [| |[]] [| |[]]; cbn; try discriminate. eauto. Qed.

Lemma gt_trans : forall t u v w, gt t u v = true -> gt t v w = true -> gt t u w = true.
Proof.
 induction t as [|k t IH]; intros u v w; [reflexivity|]. rewrite !gt_cons.
 intros [A1 B1] [A2 B2]. split; [intros i L; exact (agree_trans _ _ _ (A1 i L) (A2 i L))|].
 destruct B1 as [B1|B1], B2 as [B2|B2].
 - left. exact (agree_trans _ _ _ B1 B2).
 - right. destruct (ptrb_shape _ _ _ B2) as [a [b [X [Y G]]]]. rewrite X in B1.
   rewrite (agree_vec _ _ B1), Y. exact G.
 - right. destruct (ptrb_shape _ _ _ B1) as [a [b [X [Y G]]]]. rewrite Y in B2.
   apply agree_sym in B2. rewrite X, (agree_vec _ _ B2). exact G.
 - right. destruct (ptrb_shape _ _ _ B1) as [a [b [X [Y G]]]].
   destruct (ptrb_shape _ _ _ B2) as [b' [c [X' [Y' G']]]].
   rewrite Y in X'. injection X' as <-. rewrite X, Y'. exact (IH _ _ _ G G').
Qed.

Lemma gt_mono : forall t t' u v, ltl t t' = true -> gt t' u v = true -> gt t u v = true.
Proof.
 induction t as [|k s IH]; intros t' u v L G; [reflexivity|].
 destruct t' as [|k' s']; [discriminate L|]. apply ltl_cons in L. rewrite gt_cons in G |- *.
 destruct G as [A B]. destruct L as [L|[<- L]].
 - split; [intros i Li; apply A; lia|]. left. apply A. exact L.
 - split; [exact A|]. destruct B as [B|B]; [left; exact B|right].
   destruct (ptrb_shape _ _ _ B) as [a [b [X [Y G]]]]. rewrite X, Y. exact (IH _ _ _ L G).
Qed.

Lemma E_nil : forall u v, E [] u v = true.
Proof. intros. unfold E. cbn [gt]. apply orb_true_r. Qed.
Lemma E_refl : forall t u, E t u u = true.
Proof. intros. unfold E. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma E_sym : forall t u v, E t u v = true -> E t v u = true.
Proof.
 unfold E. intros t u v H. apply orb_true_iff in H as [H|H]; apply orb_true_iff.
 - left. rewrite Nat.eqb_sym. exact H.
 - right. exact (gt_sym _ _ _ H).
Qed.
Lemma E_trans : forall t u v w, E t u v = true -> E t v w = true -> E t u w = true.
Proof.
 unfold E. intros t u v w H1 H2. apply orb_true_iff in H1, H2. apply orb_true_iff.
 destruct H1 as [H1|H1]; [apply Nat.eqb_eq in H1; subst v; destruct H2; auto|].
 destruct H2 as [H2|H2]; [apply Nat.eqb_eq in H2; subst w; auto|].
 right. exact (gt_trans _ _ _ _ H1 H2).
Qed.
Lemma E_mono : forall t t' u v, ltl t t' = true -> E t' u v = true -> E t u v = true.
Proof.
 unfold E. intros t t' u v L H. apply orb_true_iff in H as [H|H]; apply orb_true_iff; [auto|].
 right. exact (gt_mono _ _ _ _ L H).
Qed.

(* ======================= stop paths along a walk ======================= *)
Definition stopidx (u v : nat) : nat := match fstop (ctk u) (ctk v) with Some (k, _) => k | None => 0 end.

Fixpoint path (W : list (nat * nat)) : list nat := match W with
 | [] => []
 | (u, v) :: W' => stopidx u v :: path W' end.

Fixpoint thrs (W : list (nat * nat)) : list (list nat) := match W with
 | [] => []
 | _ :: W' => path W :: thrs W' end.

Definition witness (t : list nat) : Prop := t <> [] /\ exists x y, In x Sc /\ In y Sc /\
 E t x y = false /\ forall t', ltl t' t = true -> E t' x y = true.

Lemma walk_witness : forall W, walk W -> forall u v W', W = (u, v) :: W' ->
 In u Sc /\ In v Sc /\ E (path W) u v = false /\ forall t', ltl t' (path W) = true -> E t' u v = true.
Proof.
 induction 1 as [u v k r D Iu Iv F|u v k a b W D Iu Iv F Hw IH]; intros u' v' W' Q;
  injection Q as <- <- <-; cbn [path]; unfold stopidx; rewrite F;
  pose proof (fstop_spec (ctk u) (ctk v)) as Sp; rewrite F in Sp; cbn in Sp;
  destruct Sp as [A [T C]].
 - split; [exact Iu|split; [exact Iv|split]].
   + unfold E. apply orb_false_iff. split; [apply Nat.eqb_neq; exact D|].
     apply Bool.not_true_iff_false. rewrite gt_cons. intros [_ [B|B]].
     * unfold agreeb in B. rewrite T in B. discriminate B.
     * destruct (ptrb_shape _ _ _ B) as [a [b [X [Y _]]]]. rewrite X, Y, tev_vec in T.
       destruct (Nat.eqb a b); discriminate T.
   + intros [|k' s] L; [apply E_nil|]. apply ltl_cons in L as [L|[_ L]]; [|destruct s; discriminate L].
     unfold E. apply orb_true_iff. right. rewrite gt_cons. split; [intros i Li; apply A; lia|].
     left. apply A. exact L.
 - destruct (IH a b W eq_refl) as [Ia [Ib [Nab Lab]]]. fold (path ((a, b) :: W)).
   pose proof T as T'. apply tev_ptr in T' as [X [Y Dab]].
   split; [exact Iu|split; [exact Iv|split]].
   + unfold E. apply orb_false_iff. split; [apply Nat.eqb_neq; exact D|].
     apply Bool.not_true_iff_false. rewrite gt_cons. intros [_ [B|B]].
     * unfold agreeb in B. rewrite T in B. discriminate B.
     * rewrite X, Y in B. cbn [ptrb] in B. unfold E in Nab. cbn [path] in Nab. unfold stopidx in Nab. rewrite B, orb_true_r in Nab. discriminate Nab.
   + intros [|k' s] L; [apply E_nil|]. apply ltl_cons in L as [L|[<- L]].
     * unfold E. apply orb_true_iff. right. rewrite gt_cons. split; [intros i Li; apply A; lia|].
       left. apply A. exact L.
     * unfold E. apply orb_true_iff. right. rewrite gt_cons. split; [exact A|]. right.
       rewrite X, Y. cbn [ptrb]. specialize (Lab s L). unfold E in Lab.
       apply orb_true_iff in Lab as [Lab|Lab]; [apply Nat.eqb_eq in Lab; contradiction|exact Lab].
Qed.

Lemma walk_tail : forall p W, walk (p :: W) -> W = [] \/ walk W.
Proof. intros p W H. inversion H; subst; auto. Qed.

Lemma thrs_witness : forall W, walk W -> forall t, In t (thrs W) -> witness t.
Proof.
 induction W as [|[u v] W IH]; intros Hw t I; [destruct I|]. destruct I as [<-|I].
 - destruct (walk_witness _ Hw u v W eq_refl) as [Iu [Iv [N L]]].
   split; [discriminate|]. exists u, v. auto.
 - destruct (walk_tail _ _ Hw) as [->|Hw']; [destruct I|exact (IH Hw' t I)].
Qed.

Lemma path_length : forall W, length (path W) = length W.
Proof. induction W as [|[u v] W IH]; cbn; congruence. Qed.

Lemma thrs_length : forall W, length (thrs W) = length W.
Proof. induction W as [|p W IH]; cbn; congruence. Qed.

Lemma thrs_short : forall W t, In t (thrs W) -> length t <= length W.
Proof.
 induction W as [|p W IH]; intros t I; [destruct I|]. destruct I as [<-|I].
 - rewrite path_length. reflexivity.
 - cbn. specialize (IH t I). lia.
Qed.

Lemma thrs_nodup : forall W, NoDup (thrs W).
Proof.
 induction W as [|p W IH]; cbn [thrs]; constructor; [|exact IH].
 intro I. apply thrs_short in I. rewrite path_length in I. cbn [length] in I. lia.
Qed.

(* ======================= strict refinement ======================= *)
Lemma count_thresholds : Sc <> [] -> forall n T, length T = n -> NoDup T -> (forall t, In t T -> witness t) ->
 n + 1 <= ncls_aux (E (maxl T)) [] Sc.
Proof.
 intro Sne. induction n as [|n IH]; intros T Ln ND Wt.
 - destruct Sc as [|x xs]; [congruence|]. pose proof (ncls_pos (E (maxl T)) x xs). lia.
 - assert (Tne : T <> []) by (intros ->; discriminate Ln).
   pose proof (maxl_in T Tne) as Im. remember (maxl T) as m eqn:Em.
   destruct (in_split m T Im) as [T1 [T2 ->]].
   pose proof (NoDup_remove_1 _ _ _ ND) as ND'. pose proof (NoDup_remove_2 _ _ _ ND) as Nm.
   assert (Sub : forall t, In t (T1 ++ T2) -> In t (T1 ++ m :: T2))
     by (intros t I; rewrite in_app_iff in *; cbn; tauto).
   assert (L' : length (T1 ++ T2) = n) by (rewrite app_length in Ln |- *; cbn in Ln; lia).
   specialize (IH (T1 ++ T2) L' ND' (fun t I => Wt t (Sub t I))).
   destruct (Wt m Im) as [Mne [x [y [Ix [Iy [Sep Join]]]]]].
   assert (Lt : ltl (maxl (T1 ++ T2)) m = true).
   { destruct (list_eq_dec (list_eq_dec Nat.eq_dec) (T1 ++ T2) []) as [Q|Q].
     { rewrite Q. cbn [maxl]. apply ltl_nil_l. exact Mne. }
     assert (I : In (maxl (T1 ++ T2)) (T1 ++ T2)) by (apply maxl_in; exact Q).
     destruct (maxl_ge _ _ (Sub _ I)) as [Eq|Lt]; [|rewrite <- Em in Lt; exact Lt].
     rewrite <- Em in Eq. rewrite Eq in I. contradiction. }
   pose proof (ncls_strict (E (maxl (T1 ++ T2))) (E m) (fun a b => E_mono _ _ a b Lt)
     (E_sym _) (E_trans _) (E_refl _) (E_sym _) (E_trans _) Sc x y Ix Iy (Join _ Lt) Sep).
   lia.
Qed.

Theorem walk_bound_sec : forall d p q b, p <> q -> In p Sc -> In q Sc -> cellcmp R P h d p q = Some b ->
 cellcmp R P h (pred (length Sc)) p q = Some b.
Proof.
 intros d p q b D Ip Iq H. destruct (walk_of_answer d p q b D Ip Iq H) as [W [Hw Hc]].
 assert (Sne : Sc <> []) by (intros ->; destruct Ip).
 pose proof (count_thresholds Sne _ (thrs ((p, q) :: W)) eq_refl (thrs_nodup _) (thrs_witness _ Hw)) as C.
 rewrite thrs_length in C. pose proof (ncls_le (E (maxl (thrs ((p, q) :: W)))) Sc []) as M.
 cbn [length] in C. apply (cellcmp_mono R P h (S (length W))); [lia|exact Hc].
Qed.
End Walk.

(* ======================= the published statements ======================= *)
Theorem walk_bound_pred : forall R P h S,
 (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->
 (forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true) ->
 closed_in h S -> no_true_pairs R P h S ->
 forall d p q b, p <> q -> In p S -> In q S -> cellcmp R P h d p q = Some b ->
 cellcmp R P h (pred (length S)) p q = Some b.
Proof. intros R P h S Sy Tr Cl Nt. exact (walk_bound_sec R P h Sy Tr S Cl Nt). Qed.

Theorem walk_bound : forall R P h S,
 (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->
 (forall x y z, num_cmp P PEqual x y = true -> num_cmp P PEqual y z = true -> num_cmp P PEqual x z = true) ->
 closed_in h S -> no_true_pairs R P h S ->
 forall d p q b, p <> q -> In p S -> In q S -> cellcmp R P h d p q = Some b ->
 cellcmp R P h (length S) p q = Some b.
Proof.
 intros R P h S Sy Tr Cl Nt d p q b D Ip Iq H.
 apply (cellcmp_mono R P h (pred (length S))); [lia|exact (walk_bound_pred R P h S Sy Tr Cl Nt d p q b D Ip Iq H)].
Qed.

(* ======================= the transitivity hypothesis is needed ======================= *)
(* JitEqBudget's h5 under `tol` (symmetric, not transitive): S is all five cells, it is closed and
   has no true pairs, yet cells 1 and 3 answer Some false at budget 6 and None at budget 5. *)
Definition S5 : list nat := [0; 1; 2; 3; 4].

Lemma h5_closed : closed_in h5 S5.
Proof.
 intros p xs Ip Hp l Il. destruct Ip as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn in Hp; injection Hp as <-;
  cbn in Il; destruct Il as [<-|[]]; cbn; tauto.
Qed.

Definition nxt (p : nat) : nat := match p with 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | _ => 1 end.
Definition lab (p : nat) : N := match p with 0 => 0%N | 1 | 2 => 1%N | _ => 2%N end.

Lemma cell_step : forall R P h l1 n1 l2 n2 d,
 list_eq (eq_depth_r R P h (S d)) (cell l1 n1) (cell l2 n2) =
 if num_cmp P PEqual (NFloat l1) (NFloat l2)
 then (if Nat.eqb n1 n2 then Some true else cellcmp R P h d n1 n2) else Some false.
Proof.
 intros. unfold cell.
 change (list_eq (eq_depth_r R P h (S d)) [VNum (NFloat l1); VVec n1] [VNum (NFloat l2); VVec n2]) with
   (match Some (num_cmp P PEqual (NFloat l1) (NFloat l2)) with
    | Some true => match (if Nat.eqb n1 n2 then Some true else cellcmp R P h d n1 n2) with
                   | Some true => Some true | r => r end
    | r => r end).
 destruct (num_cmp P PEqual (NFloat l1) (NFloat l2)); [|reflexivity].
 destruct (Nat.eqb n1 n2); [reflexivity|]. destruct (cellcmp R P h d n1 n2) as [[|]|]; reflexivity.
Qed.

Lemma in_S5 : forall p, In p S5 -> p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4.
Proof. intros p I. unfold S5 in I. destruct I as [<-|[<-|[<-|[<-|[<-|[]]]]]]; auto. Qed.

Lemma h5_cell : forall R d p, In p S5 ->
 forall q, In q S5 -> cellcmp R tol h5 (S d) p q =
 list_eq (eq_depth_r R tol h5 (S d)) (cell (lab p) (nxt p)) (cell (lab q) (nxt q)).
Proof.
 intros R d p Ip q Iq.
 destruct (in_S5 p Ip) as [-> | [-> | [-> | [-> | ->]]]]; destruct (in_S5 q Iq) as [-> | [-> | [-> | [-> | ->]]]];
  reflexivity.
Qed.

Lemma nxt_S5 : forall p, In p S5 -> In (nxt p) S5.
Proof. intros p Ip. destruct (in_S5 p Ip) as [-> | [-> | [-> | [-> | ->]]]]; cbn; tauto. Qed.

Lemma nxt_inj : forall p q, In p S5 -> In q S5 -> p <> q -> nxt p <> nxt q.
Proof.
 intros p q Ip Iq D.
 destruct (in_S5 p Ip) as [-> | [-> | [-> | [-> | ->]]]]; destruct (in_S5 q Iq) as [-> | [-> | [-> | [-> | ->]]]];
  cbn; congruence.
Qed.

Lemma h5_no_true : forall R, no_true_pairs R tol h5 S5.
Proof.
 intros R d. induction d as [|d IH]; intros p q Ip Iq D.
 - destruct (in_S5 p Ip) as [-> | [-> | [-> | [-> | ->]]]]; destruct (in_S5 q Iq) as [-> | [-> | [-> | [-> | ->]]]];
    cbn; discriminate.
 - rewrite (h5_cell R d p Ip q Iq), cell_step.
   destruct (num_cmp tol PEqual _ _); [|discriminate].
   destruct (Nat.eqb_spec (nxt p) (nxt q)) as [E|_]; [exfalso; exact (nxt_inj p q Ip Iq D E)|].
   apply IH; [apply nxt_S5; exact Ip|apply nxt_S5; exact Iq|exact (nxt_inj p q Ip Iq D)].
Qed.

Definition walk_bound_no_trans_statement : Prop := forall R P h S,
 (forall x y, num_cmp P PEqual x y = num_cmp P PEqual y x) ->
 closed_in h S -> no_true_pairs R P h S ->
 forall d p q b, p <> q -> In p S -> In q S -> cellcmp R P h d p q = Some b ->
 cellcmp R P h (length S) p q = Some b.

Theorem walk_bound_needs_trans : ~ walk_bound_no_trans_statement.
Proof.
 intro H. pose (R := agreed_rules).
 assert (A6 : cellcmp R tol h5 6 1 3 = Some false) by (vm_compute; reflexivity).
 assert (A5 : cellcmp R tol h5 5 1 3 = None) by (vm_compute; reflexivity).
 pose proof (H R tol h5 S5 tol_symmetric h5_closed (h5_no_true R) 6 1 3 false
   ltac:(discriminate) ltac:(cbn; tauto) ltac:(cbn; tauto) A6) as C.
 cbn [length S5] in C. rewrite A5 in C. discriminate C.
Qed.

End JitEqBudgetWalk.
