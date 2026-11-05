(* The supported CL reader AST, not a claim about arbitrary Common Lisp.
   Source provenance and native execution are tested by check-cl-port.sh. *)
From Coq Require Import String List Bool Arith.
Import ListNotations.
Open Scope string_scope.
Module CLPortGuard.
Inductive sexp := Sym (name : string) | Text (text : string) | Nil | Pair (a b : sexp).
Fixpoint list (xs : Datatypes.list sexp) := match xs with [] => Nil | x::xs => Pair x (list xs) end.
Definition cl s := Sym ("COMMON-LISP:" ++ s).
Definition sh s := Sym ("SHEN:" ++ s).
Definition call f xs := Pair f (list xs).
Definition quote x := call (cl "QUOTE") [x].
Definition expected := call (cl "DEFUN") [sh "shen-cl.true?"; list [sh "X"];
 call (cl "COND")
  [list [call (cl "EQ") [quote (sh "true"); sh "X"]; quote (cl "T")];
   list [call (cl "EQ") [quote (sh "false"); sh "X"]; Nil];
   list [cl "T"; call (sh "simple-error")
      [call (cl "FORMAT") [Nil; Text "boolean expected: not ~A~%"; sh "X"]]]]].
Fixpoint sexp_eq a b := match a,b with
| Sym a, Sym b | Text a, Text b => String.eqb a b
| Nil, Nil => true
| Pair a b, Pair c d => sexp_eq a c && sexp_eq b d
| _,_ => false end.
Lemma sexp_eq_sound : forall a b, sexp_eq a b = true -> a = b.
Proof.
 induction a; destruct b; simpl; intros H; try discriminate;
 try (apply String.eqb_eq in H; subst; reflexivity).
 - reflexivity.
 - apply andb_true_iff in H as [H1 H2]. rewrite (IHa1 _ H1), (IHa2 _ H2). reflexivity.
Qed.
Definition admitted root := sexp_eq root expected.
Theorem admission_exact : forall root, admitted root = true -> root = expected.
Proof. intros. apply sexp_eq_sound. exact H. Qed.

(* Other indexes arbitrary nonboolean Shen objects. This quotient deliberately
   abstracts identity/layout and diagnostic text, not booleans versus NIL. *)
Inductive value := ShenTrue | ShenFalse | Other (object_id : nat) | HostTrue | HostNil | Diagnostic.
Inductive result := Returned (v : value) | BooleanError | Unsupported.
Definition input (n : nat) := Other n.
Definition eq_value a b := match a,b with
| ShenTrue, ShenTrue | ShenFalse, ShenFalse | HostTrue, HostTrue | HostNil, HostNil => true
| _,_ => false end.
Fixpoint eval (fuel : nat) (x : value) (e : sexp) : result :=
 match fuel with 0 => Unsupported | S fuel =>
 match e with
 | Nil => Returned HostNil
 | Sym "SHEN:X" => Returned x
 | Sym "COMMON-LISP:T" => Returned HostTrue
 | Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "SHEN:true") Nil) => Returned ShenTrue
 | Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "SHEN:false") Nil) => Returned ShenFalse
 | Pair (Sym "COMMON-LISP:QUOTE") (Pair (Sym "COMMON-LISP:T") Nil) => Returned HostTrue
 | Pair (Sym "COMMON-LISP:EQ") (Pair a (Pair b Nil)) =>
   match eval fuel x a, eval fuel x b with
   | Returned a, Returned b => Returned (if eq_value a b then HostTrue else HostNil)
   | BooleanError, _ | _, BooleanError => BooleanError
   | _,_ => Unsupported end
 | Pair (Sym "COMMON-LISP:COND") Nil => Returned HostNil
 | Pair (Sym "COMMON-LISP:COND") (Pair (Pair test (Pair yes Nil)) rest) =>
   match eval fuel x test with
   | Returned HostNil => eval fuel x (Pair (cl "COND") rest)
   | Returned _ => eval fuel x yes
   | BooleanError => BooleanError | Unsupported => Unsupported end
 | Pair (Sym "COMMON-LISP:FORMAT") (Pair Nil (Pair (Text "boolean expected: not ~A~%") (Pair (Sym "SHEN:X") Nil))) => Returned Diagnostic
 | Pair (Sym "SHEN:simple-error") (Pair message Nil) =>
   match eval fuel x message with Returned Diagnostic => BooleanError | _ => Unsupported end
 | _ => Unsupported end end.
Definition body root := match root with
 | Pair (Sym "COMMON-LISP:DEFUN") (Pair (Sym "SHEN:shen-cl.true?") (Pair (Pair (Sym "SHEN:X") Nil) (Pair b Nil))) => Some b
 | _ => None end.
Definition run root x := match body root with Some b => eval 20 x b | None => Unsupported end.
Definition strict_guard x := match x with ShenTrue => Returned HostTrue | ShenFalse => Returned HostNil | _ => BooleanError end.
Theorem actual_guard_refinement : forall root x,
 admitted root = true -> run root x = strict_guard x.
Proof. intros root x H. apply admission_exact in H. subst root. destruct x; reflexivity. Qed.

(* Observations carry arbitrary state, events and failure values through the
   chosen continuation. Neither rejected input nor the unchosen branch runs. *)
Definition source_if {S R : Type} (x : value) (s : S) (yes no : S -> R) (bad : S -> R) :=
 match x with ShenTrue => yes s | ShenFalse => no s | _ => bad s end.
Definition compiled_if {S R : Type} root x (s : S) (yes no bad : S -> R) :=
 match run root x with Returned HostTrue => Some (yes s) | Returned HostNil => Some (no s)
 | BooleanError => Some (bad s) | _ => None end.
Theorem conditional_refinement : forall (S R : Type) root x (s : S) (yes no bad : S -> R),
 admitted root = true -> compiled_if root x s yes no bad = Some (source_if x s yes no bad).
Proof. intros. unfold compiled_if. rewrite actual_guard_refinement by assumption. destruct x; reflexivity. Qed.
Theorem other_values_rejected : forall root n, admitted root = true -> run root (Other n) = BooleanError.
Proof. intros. rewrite actual_guard_refinement by assumption. reflexivity. Qed.
End CLPortGuard.
