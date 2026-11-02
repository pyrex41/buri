(* E2E-22: an inert reader for the Chez Scheme text this lane checks.

   It reads the define-language forms of Chez 10.3.0 s/np-languages.ss and the
   output Chez's own printer produced for traced nanopass passes
   (print-gensym 'pretty/suffix, print-graph #t).  It covers exactly the
   lexical forms that occur there:
     ( ... ) [ ... ]   lists, with an optional dotted tail
     #( ... )          vectors           #[ ... ]  records
     #{ ... }          gensym syntax     #< ... >  opaque printed objects
     #n= d  #n#        print-graph labels and references
     quote-d           quote             strings   double-quoted, backslash escapes
     ; ...             comments          atoms     everything else
   Anything else makes [read_one] fail; the reader never evaluates. *)
From Coq Require Import String Ascii List Bool Arith ZArith.
Import ListNotations.
Open Scope string_scope.

Inductive sexp : Type :=
| Atom : string -> sexp
| Str : string -> sexp
| Lst : list sexp -> sexp
| Dot : list sexp -> sexp -> sexp
| Vec : list sexp -> sexp
| Rec : list sexp -> sexp
| Def : nat -> sexp -> sexp
| Ref : nat -> sexp.

Definition sexp_eq_dec : forall x y : sexp, {x = y} + {x <> y}.
Proof.
  fix IH 1; intros x y; decide equality;
    try apply string_dec; try apply Nat.eq_dec;
    try (apply list_eq_dec; exact IH).
Defined.

Definition sexp_eqb (x y : sexp) : bool := if sexp_eq_dec x y then true else false.

Lemma sexp_eqb_true : forall x y, sexp_eqb x y = true -> x = y.
Proof. unfold sexp_eqb; intros x y; destruct (sexp_eq_dec x y); congruence. Qed.

Definition chr (n : nat) : ascii := ascii_of_nat n.
Definition is (c : ascii) (n : nat) : bool := Nat.eqb (nat_of_ascii c) n.

Definition is_space (c : ascii) : bool :=
  is c 32 || is c 10 || is c 9 || is c 13 || is c 12.

(* parentheses, brackets, double quote, semicolon, single quote *)
Definition is_delim (c : ascii) : bool :=
  is_space c || is c 40 || is c 41 || is c 91 || is c 93 || is c 34 || is c 59 || is c 39.

Definition is_digit (c : ascii) : bool :=
  Nat.leb 48 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 57.

Fixpoint skip_ws (s : string) : string :=
  match s with
  | String c r =>
      if is_space c then skip_ws r
      else if is c 59 then skip_comment r
      else s
  | EmptyString => s
  end
with skip_comment (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c r => if is c 10 then skip_ws r else skip_comment r
  end.

Fixpoint take_atom (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c r =>
      if is_delim c then (EmptyString, s)
      else let (a, rest) := take_atom r in (String c a, rest)
  end.

(* Characters up to (not including) [stop]; the stop character is consumed. *)
Fixpoint take_until (stop : nat) (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c r =>
      if is c stop then Some (EmptyString, r)
      else match take_until stop r with
           | Some (a, rest) => Some (String c a, rest)
           | None => None
           end
  end.

Fixpoint take_string (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c r =>
      if is c 34 then Some (EmptyString, r)
      else if is c 92 then
        match r with
        | String c2 r2 =>
            match take_string r2 with
            | Some (a, rest) => Some (String c2 a, rest)
            | None => None
            end
        | EmptyString => None
        end
      else match take_string r with
           | Some (a, rest) => Some (String c a, rest)
           | None => None
           end
  end.

Fixpoint take_digits (s : string) : string * string :=
  match s with
  | String c r =>
      if is_digit c then let (d, rest) := take_digits r in (String c d, rest)
      else (EmptyString, s)
  | EmptyString => (EmptyString, EmptyString)
  end.

Fixpoint digits_nat_acc (acc : nat) (s : string) : nat :=
  match s with
  | EmptyString => acc
  | String c r => digits_nat_acc (acc * 10 + (nat_of_ascii c - 48)) r
  end.

Definition digits_nat (s : string) : nat := digits_nat_acc 0 s.

Fixpoint read_one (fuel : nat) (s : string) : option (sexp * string) :=
  match fuel with
  | O => None
  | S f =>
      match skip_ws s with
      | EmptyString => None
      | String c r =>
          if is c 40 then
            match read_seq f 41 true r with
            | Some (xs, None, rest) => Some (Lst xs, rest)
            | Some (xs, Some t, rest) => Some (Dot xs t, rest)
            | None => None
            end
          else if is c 91 then
            match read_seq f 93 true r with
            | Some (xs, None, rest) => Some (Lst xs, rest)
            | Some (xs, Some t, rest) => Some (Dot xs t, rest)
            | None => None
            end
          else if is c 41 || is c 93 then None
          else if is c 39 then
            match read_one f r with
            | Some (x, rest) => Some (Lst [Atom "quote"; x], rest)
            | None => None
            end
          else if is c 34 then
            match take_string r with
            | Some (t, rest) => Some (Str t, rest)
            | None => None
            end
          else if is c 35 then
            match r with
            | String c2 r2 =>
                if is c2 91 then
                  match read_seq f 93 false r2 with
                  | Some (xs, None, rest) => Some (Rec xs, rest)
                  | _ => None
                  end
                else if is c2 40 then
                  match read_seq f 41 false r2 with
                  | Some (xs, None, rest) => Some (Vec xs, rest)
                  | _ => None
                  end
                else if is c2 123 then
                  match take_until 125 r2 with
                  | Some (a, rest) => Some (Atom ("#{" ++ a ++ "}"), rest)
                  | None => None
                  end
                else if is c2 60 then
                  match take_until 62 r2 with
                  | Some (a, rest) => Some (Atom ("#<" ++ a ++ ">"), rest)
                  | None => None
                  end
                else if is_digit c2 then
                  let (ds, r3) := take_digits r in
                  match r3 with
                  | String c3 r4 =>
                      if is c3 61 then
                        match read_one f r4 with
                        | Some (x, rest) => Some (Def (digits_nat ds) x, rest)
                        | None => None
                        end
                      else if is c3 35 then Some (Ref (digits_nat ds), r4)
                      else None
                  | EmptyString => None
                  end
                else
                  let (a, rest) := take_atom r2 in Some (Atom (String c (String c2 a)), rest)
            | EmptyString => None
            end
          else
            let (a, rest) := take_atom (String c r) in
            match a with
            | EmptyString => None
            | _ => Some (Atom a, rest)
            end
      end
  end
with read_seq (fuel : nat) (close : nat) (dots : bool) (s : string)
  : option (list sexp * option sexp * string) :=
  match fuel with
  | O => None
  | S f =>
      match skip_ws s with
      | EmptyString => None
      | String c r =>
          if is c close then Some ([], None, r)
          else
            let dot_here :=
              dots && is c 46 &&
              match r with String c2 _ => is_delim c2 | EmptyString => false end in
            if dot_here then
              match read_one f r with
              | Some (t, rest) =>
                  match skip_ws rest with
                  | String c3 rest2 => if is c3 close then Some ([], Some t, rest2) else None
                  | EmptyString => None
                  end
              | None => None
              end
            else
              match read_one f (String c r) with
              | Some (x, rest) =>
                  match read_seq f close dots rest with
                  | Some (xs, t, rest2) => Some (x :: xs, t, rest2)
                  | None => None
                  end
              | None => None
              end
      end
  end.

(* Read exactly one datum; only whitespace and comments may follow. *)
Definition read_exactly (s : string) : option sexp :=
  match read_one (2 * String.length s + 2) s with
  | Some (x, rest) =>
      match skip_ws rest with
      | EmptyString => Some x
      | _ => None
      end
  | None => None
  end.

(* ---- lines ---------------------------------- *)

Fixpoint string_of_rev (acc : string) (cs : list ascii) : string :=
  match cs with
  | [] => acc
  | c :: r => string_of_rev (String c acc) r
  end.

(* [cur] holds the current line's characters in reverse. *)
Fixpoint split_lines_acc (cur : list ascii) (s : string) : list string :=
  match s with
  | EmptyString => [string_of_rev EmptyString cur]
  | String c r =>
      if is c 10 then string_of_rev EmptyString cur :: split_lines_acc [] r
      else split_lines_acc (c :: cur) r
  end.

Definition split_lines (s : string) : list string := split_lines_acc [] s.

(* ---- print-graph labels ------------------------------------------------ *)

(* Collect every #n= definition (outermost first). *)
Fixpoint defs (x : sexp) : list (nat * sexp) :=
  let fix defs_list (xs : list sexp) : list (nat * sexp) :=
    match xs with [] => [] | y :: ys => app (defs y) (defs_list ys) end in
  match x with
  | Def n y => (n, y) :: defs y
  | Lst xs | Vec xs | Rec xs => defs_list xs
  | Dot xs t => app (defs_list xs) (defs t)
  | _ => []
  end.

Fixpoint lookup_def (n : nat) (ds : list (nat * sexp)) : option sexp :=
  match ds with
  | [] => None
  | (m, y) :: r => if Nat.eqb n m then Some y else lookup_def n r
  end.

(* Replace references by their definitions, removing labels.  Fuel bounds
   the unfolding depth, so cyclic graphs are rejected (None), never looped. *)
Fixpoint unshare (fuel : nat) (ds : list (nat * sexp)) (x : sexp) : option sexp :=
  match fuel with
  | O => None
  | S f =>
      let fix go_list (xs : list sexp) : option (list sexp) :=
        match xs with
        | [] => Some []
        | y :: ys =>
            match unshare f ds y, go_list ys with
            | Some y', Some ys' => Some (y' :: ys')
            | _, _ => None
            end
        end in
      match x with
      | Def _ y => unshare f ds y
      | Ref n => match lookup_def n ds with Some y => unshare f ds y | None => None end
      | Lst xs => option_map Lst (go_list xs)
      | Vec xs => option_map Vec (go_list xs)
      | Rec xs => option_map Rec (go_list xs)
      | Dot xs t =>
          match go_list xs, unshare f ds t with
          | Some xs', Some t' => Some (Dot xs' t')
          | _, _ => None
          end
      | _ => Some x
      end
  end.

(* Reference-free form of an acyclic printed datum. *)
Definition expand_graph (x : sexp) : option sexp := unshare 64 (defs x) x.
