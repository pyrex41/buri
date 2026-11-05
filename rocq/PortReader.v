(* E2E-17: an independent, rejecting reader for the exact byte excerpts of
   pinned port primitive definitions (rocq/PrimitiveSources.v). It reads
   parentheses, strings with backslash escapes, quote, line comments, and (in
   Common Lisp mode) |bar| symbols with every other symbol upcased and NIL read
   as the empty list. Nothing is evaluated: #. and #' are inert atom text.
   It validates these source excerpts; it is not a proof of the Chez or SBCL
   reader (those remain named host contracts, docs/PRIMITIVES.md). *)
From Coq Require Import String Ascii List Bool.
From Buri Require CLLowering.
Import ListNotations.
Open Scope string_scope.
Module PortReader.
Notation sv := CLLowering.sv.
Notation VSym := CLLowering.VSym.
Notation VStr := CLLowering.VStr.
Notation VNum := CLLowering.VNum.
Notation VNil := CLLowering.VNil.
Notation VCons := CLLowering.VCons.

Inductive tok := TOpen | TClose | TQuote | TStr (s : string) | TAtom (s : string) | TBar (s : string).
Definition nl := ascii_of_nat 10.
Definition dq := ascii_of_nat 34.
Definition bs := ascii_of_nat 92.
Definition is_space c := (Ascii.eqb c " " || Ascii.eqb c nl || Ascii.eqb c (ascii_of_nat 13)
 || Ascii.eqb c (ascii_of_nat 9))%bool.
Definition is_delim (cl : bool) c := (is_space c || Ascii.eqb c "(" || Ascii.eqb c ")"
 || Ascii.eqb c "[" || Ascii.eqb c "]" || Ascii.eqb c dq || Ascii.eqb c ";"
 || Ascii.eqb c "'" || (cl && Ascii.eqb c "|"))%bool.
Fixpoint skip_line s := match s with
 | EmptyString => EmptyString | String c r => if Ascii.eqb c nl then r else skip_line r end.
Fixpoint word cl s : string * string := match s with
 | EmptyString => (EmptyString, EmptyString)
 | String c r => if is_delim cl c then (EmptyString, s) else let '(a, b) := word cl r in (String c a, b) end.
Fixpoint str_lit s : option (string * string) := match s with
 | EmptyString => None
 | String c r => if Ascii.eqb c dq then Some (EmptyString, r)
   else if Ascii.eqb c bs then match r with
     | String d r' => match str_lit r' with Some (a, b) => Some (String d a, b) | None => None end
     | EmptyString => None end
   else match str_lit r with Some (a, b) => Some (String c a, b) | None => None end end.
Fixpoint bar s : option (string * string) := match s with
 | EmptyString => None
 | String c r => if Ascii.eqb c "|" then Some (EmptyString, r)
   else match bar r with Some (a, b) => Some (String c a, b) | None => None end end.
Fixpoint lex (fuel : nat) (cl : bool) (s : string) : option (list tok) := match fuel with
 | O => None
 | S n => match s with
   | EmptyString => Some []
   | String c r =>
     if is_space c then lex n cl r
     else if Ascii.eqb c ";" then lex n cl (skip_line r)
     else if (Ascii.eqb c "(" || Ascii.eqb c "[")%bool then option_map (cons TOpen) (lex n cl r)
     else if (Ascii.eqb c ")" || Ascii.eqb c "]")%bool then option_map (cons TClose) (lex n cl r)
     else if Ascii.eqb c "'" then option_map (cons TQuote) (lex n cl r)
     else if Ascii.eqb c dq then match str_lit r with
       | Some (a, b) => option_map (cons (TStr a)) (lex n cl b) | None => None end
     else if (cl && Ascii.eqb c "|")%bool then match bar r with
       | Some (a, b) => option_map (cons (TBar a)) (lex n cl b) | None => None end
     else let '(a, b) := word cl s in match a with
       | EmptyString => None | _ => option_map (cons (TAtom a)) (lex n cl b) end
   end end.

Definition digit c := let n := nat_of_ascii c in (Nat.leb 48 n && Nat.leb n 57)%bool.
Fixpoint all_digits s := match s with
 | EmptyString => false
 | String c EmptyString => digit c
 | String c r => (digit c && all_digits r)%bool end.
Definition numeric s := match s with
 | String c r => if Ascii.eqb c "-" then all_digits r else all_digits s
 | EmptyString => false end.
(* A decimal token: digits and dots with at least one digit, optional sign. *)
Fixpoint decimal_chars s := match s with
 | EmptyString => true
 | String c r => ((digit c || Ascii.eqb c ".") && decimal_chars r)%bool end.
Fixpoint has_digit s := match s with EmptyString => false | String c r => (digit c || has_digit r)%bool end.
Definition decimal s := match s with
 | String c r => if Ascii.eqb c "-" then (decimal_chars r && has_digit r)%bool else (decimal_chars s && has_digit s)%bool
 | EmptyString => false end.
Definition up c := let n := nat_of_ascii c in
 if (Nat.leb 97 n && Nat.leb n 122)%bool then ascii_of_nat (n - 32) else c.
Fixpoint upcase s := match s with EmptyString => EmptyString | String c r => String (up c) (upcase r) end.
(* Decimal tokens (integers, and floats such as 1.0) are number atoms kept as
   their exact spelling; any other token is a symbol name in Scheme mode and
   an upcased symbol in CL mode. Float tokens are inert text: the admitted
   definitions pass them only to COERCE, a named host operation. *)
Definition atom (cl : bool) (a : string) : sv :=
 if decimal a then VNum a
 else if cl then (if String.eqb (upcase a) "NIL" then VNil else VSym (upcase a)) else VSym a.

Fixpoint one (fuel : nat) (cl : bool) (ts : list tok) : option (sv * list tok) := match fuel with
 | O => None
 | S n => match ts with
   | TAtom a :: r => Some (atom cl a, r)
   | TBar s :: r => Some (VSym s, r)
   | TStr s :: r => Some (VStr s, r)
   | TQuote :: r => match one n cl r with
     | Some (d, r') => Some (VCons (VSym (if cl then "QUOTE" else "quote")) (VCons d VNil), r')
     | None => None end
   | TOpen :: r => seq n cl r
   | _ => None end end
with seq (fuel : nat) (cl : bool) (ts : list tok) : option (sv * list tok) := match fuel with
 | O => None
 | S n => match ts with
   | TClose :: r => Some (VNil, r)
   | _ => match one n cl ts with
     | Some (a, r) => match seq n cl r with Some (b, r') => Some (VCons a b, r') | None => None end
     | None => None end end end.
Fixpoint forms (fuel : nat) (cl : bool) (ts : list tok) : option (list sv) := match ts with
 | [] => Some []
 | _ => match fuel with O => None | S n => match one n cl ts with
   | Some (a, r) => option_map (cons a) (forms n cl r) | None => None end end end.
Definition read (cl : bool) (s : string) : option (list sv) :=
 match lex (S (String.length s)) cl s with
 | Some ts => forms (S (List.length ts)) cl ts | None => None end.
Fixpoint to_list (v : sv) : option (list sv) := match v with
 | VNil => Some [] | VCons a b => option_map (cons a) (to_list b) | _ => None end.
End PortReader.
