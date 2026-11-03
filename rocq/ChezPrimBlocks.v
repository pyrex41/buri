(* E2E-22 (chezprim lane): a validator for np-optimize-block-order! (L16 ->
   L16), a late pass just before np-generate-code.

   In L16 a lambda is (lambda INFO (entry-block ...) (block ...)).  Blocks
   are records whose successor fields point at other block records; control
   transfers through those fields, never through a block's position in the
   list.  The list is an enumeration that np-generate-code later lays out in
   order (so fall-through and code layout do depend on it).

   [block_canon] sorts the block list of every lambda by print-graph label;
   everything else is kept.  [check_block_order] accepts when input and output
   are equal after [block_canon]: the pass changed nothing but block-list
   order.  The theorem is structural: any meaning of L16 programs that does
   not depend on block-list order (any CFG semantics that follows successor
   fields from the entry blocks) agrees on the two.  It says nothing about
   np-generate-code, whose output does depend on the order.

   The comparison is on the print-graph datum itself, without unfolding
   references: labels are numbered in printing order, and the entry list,
   which defines every block, is printed before the block list, so equal
   prefixes give equal numbering. *)
From Coq Require Import String List Bool Arith Sorting.Permutation.
From Buri Require Import ChezNpReader.
Import ListNotations.
Open Scope string_scope.

Definition ref_key (x : sexp) : nat := match x with Ref n => n | Def n _ => n | _ => 0 end.
Definition is_ref (x : sexp) : bool := match x with Ref _ => true | _ => false end.

Fixpoint insert_by_key (x : sexp) (l : list sexp) : list sexp :=
  match l with
  | [] => [x]
  | y :: r => if Nat.leb (ref_key x) (ref_key y) then x :: y :: r else y :: insert_by_key x r
  end.

Definition sort_refs (l : list sexp) : list sexp := fold_right insert_by_key [] l.

Lemma insert_by_key_perm : forall x l, Permutation (x :: l) (insert_by_key x l).
Proof.
  intros x l; induction l as [|y r IH]; simpl; [reflexivity|].
  destruct (Nat.leb (ref_key x) (ref_key y)); [reflexivity|].
  transitivity (y :: x :: r); [apply perm_swap|]. apply perm_skip, IH.
Qed.

(* Universal theorem: [sort_refs] only permutes. *)
Theorem sort_refs_perm : forall l, Permutation l (sort_refs l).
Proof.
  induction l as [|x r IH]; simpl; [reflexivity|].
  transitivity (x :: sort_refs r); [apply perm_skip, IH|apply insert_by_key_perm].
Qed.

Definition canon_last (ys : list sexp) : list sexp :=
  match rev ys with
  | Lst bs :: front => if forallb is_ref bs then rev (Lst (sort_refs bs) :: front) else ys
  | _ => ys
  end.

Fixpoint block_canon (x : sexp) : sexp :=
  let fix go (xs : list sexp) : list sexp :=
    match xs with [] => [] | y :: ys => block_canon y :: go ys end in
  match x with
  | Lst xs =>
      let ys := go xs in
      match ys with
      | Atom kw :: _ => if String.eqb kw "lambda" then Lst (canon_last ys) else Lst ys
      | _ => Lst ys
      end
  | Vec xs => Vec (go xs)
  | Rec xs => Rec (go xs)
  | Dot xs t => Dot (go xs) (block_canon t)
  | Def n y => Def n (block_canon y)
  | _ => x
  end.

Definition check_block_order (input output : sexp) : bool :=
  sexp_eqb (block_canon input) (block_canon output).

(* Universal theorem: an accepted pair has the same canonical form, so every
   meaning that factors through block-list order agrees on it. *)
Theorem check_block_order_sound :
  forall input output, check_block_order input output = true ->
    block_canon input = block_canon output /\
    forall (A : Type) (meaning : sexp -> A),
      (forall x, meaning x = meaning (block_canon x)) -> meaning input = meaning output.
Proof.
  intros input output H. apply sexp_eqb_true in H.
  split; [exact H|]. intros A meaning Hm. rewrite (Hm input), (Hm output), H. reflexivity.
Qed.
