(* E2E-06 syntax: the complete canonical KLambda surface. The Shen KLambda
   specification lists 46 primitives: 10 are special forms (evaluation order is
   not that of a call) and 36 are ordinary primitive functions. Each has a
   constructor below; `all_prims_complete` and `all_specials_complete` check that
   the enumerations are exhaustive, so no primitive can be silently absent. *)
From Coq Require Import List ZArith NArith String Ascii Bool.
From Buri Require Import Observation.
Import ListNotations.
Module KLSyntax.
Import Observation.Observation.

Definition name := text.
Fixpoint text_eqb (a b : text) : bool := match a, b with
 | [], [] => true
 | x :: a, y :: b => N.eqb x y && text_eqb a b
 | _, _ => false end.
Lemma text_eqb_eq : forall a b, text_eqb a b = true <-> a = b.
Proof.
 induction a as [|x a IH]; destruct b as [|y b]; cbn; split; intro H; try discriminate; auto.
 - apply andb_true_iff in H as [H1 H2]. apply N.eqb_eq in H1. apply IH in H2. subst; reflexivity.
 - inversion H; subst. rewrite N.eqb_refl. apply IH; reflexivity.
Qed.
Lemma text_eqb_refl : forall a, text_eqb a a = true.
Proof. intro a; apply text_eqb_eq; reflexivity. Qed.
Lemma text_eqb_neq : forall a b, text_eqb a b = false <-> a <> b.
Proof.
 intros a b; split; intro H.
 - intro E; subst; rewrite text_eqb_refl in H; discriminate.
 - destruct (text_eqb a b) eqn:E; [apply text_eqb_eq in E; contradiction|reflexivity].
Qed.

(* ASCII spelling helper; text itself is a sequence of Unicode code points. *)
Definition of_string (s : string) : text :=
 map (fun c => N.of_nat (nat_of_ascii c)) (list_ascii_of_string s).

(* Exact integers are fully specified. Inexact numbers are IEEE-754 binary64
   bit patterns; every inexact operation is a named profile slot (KLValue). *)
Inductive num := NInt (z : Z) | NFloat (bits : N).

Inductive prim :=
 | PIntern
 | PPos | PTlstr | PCn | PStr | PStringP | PNToString | PStringToN
 | PSet | PValue
 | PSimpleError | PErrorToString
 | PCons | PHd | PTl | PConsP
 | PEqual | PEvalKL
 | PAbsvector | PAddressSet | PAddressGet | PAbsvectorP
 | PWriteByte | PReadByte | POpen | PClose
 | PGetTime
 | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe | PNumberP.

Definition all_prims : list prim :=
 [PIntern; PPos; PTlstr; PCn; PStr; PStringP; PNToString; PStringToN; PSet; PValue;
  PSimpleError; PErrorToString; PCons; PHd; PTl; PConsP; PEqual; PEvalKL;
  PAbsvector; PAddressSet; PAddressGet; PAbsvectorP; PWriteByte; PReadByte; POpen; PClose;
  PGetTime; PAdd; PSub; PMul; PDiv; PGt; PLt; PGe; PLe; PNumberP].
Lemma all_prims_complete : forall p, In p all_prims.
Proof. destruct p; cbn; tauto. Qed.

Definition prim_name (p : prim) : string := match p with
 | PIntern => "intern" | PPos => "pos" | PTlstr => "tlstr" | PCn => "cn" | PStr => "str"
 | PStringP => "string?" | PNToString => "n->string" | PStringToN => "string->n"
 | PSet => "set" | PValue => "value" | PSimpleError => "simple-error"
 | PErrorToString => "error-to-string" | PCons => "cons" | PHd => "hd" | PTl => "tl"
 | PConsP => "cons?" | PEqual => "=" | PEvalKL => "eval-kl" | PAbsvector => "absvector"
 | PAddressSet => "address->" | PAddressGet => "<-address" | PAbsvectorP => "absvector?"
 | PWriteByte => "write-byte" | PReadByte => "read-byte" | POpen => "open" | PClose => "close"
 | PGetTime => "get-time" | PAdd => "+" | PSub => "-" | PMul => "*" | PDiv => "/"
 | PGt => ">" | PLt => "<" | PGe => ">=" | PLe => "<=" | PNumberP => "number?" end.

Definition prim_arity (p : prim) : nat := match p with
 | PIntern | PTlstr | PStr | PStringP | PNToString | PStringToN | PValue | PSimpleError
 | PErrorToString | PHd | PTl | PConsP | PEvalKL | PAbsvector | PAbsvectorP | PReadByte
 | PClose | PGetTime | PNumberP => 1
 | PPos | PCn | PSet | PCons | PEqual | PAddressGet | PWriteByte | POpen
 | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe => 2
 | PAddressSet => 3 end.

Inductive special := SIf | SAnd | SOr | SCond | STrapError | SDefun | SLambda | SLet | SFreeze | SType.
Definition all_specials := [SIf; SAnd; SOr; SCond; STrapError; SDefun; SLambda; SLet; SFreeze; SType].
Lemma all_specials_complete : forall s, In s all_specials.
Proof. destruct s; cbn; tauto. Qed.
Definition special_name (s : special) : string := match s with
 | SIf => "if" | SAnd => "and" | SOr => "or" | SCond => "cond" | STrapError => "trap-error"
 | SDefun => "defun" | SLambda => "lambda" | SLet => "let" | SFreeze => "freeze" | SType => "type" end.

Theorem canonical_kl_surface : List.length all_prims = 36 /\ List.length all_specials = 10 /\
 NoDup (app (map prim_name all_prims) (map special_name all_specials)).
Proof.
 split; [reflexivity|split; [reflexivity|]].
 cbn. repeat constructor; cbn; intuition discriminate.
Qed.

(* Resolved KLambda syntax. Lexical variables (EVar) and symbol literals (ESym)
   are distinguished; KLSemantics.parse performs that resolution for eval-kl. *)
Inductive expr :=
 | ENum (n : num) | EStr (t : text) | ESym (s : name) | EBool (b : bool) | ENil
 | EVar (x : name)
 | ELam (x : name) (body : expr)
 | ELet (x : name) (a body : expr)
 | EIf (c a b : expr)
 | EAnd (a b : expr) | EOr (a b : expr)
 | ECond (clauses : list (expr * expr))
 | ETrap (body handler : expr)
 | EFreeze (body : expr)
 | EType (e : expr)
 | EDefun (f : name) (params : list name) (body : expr)
 | EApp (head : expr) (args : list expr)
 | ECall (f : name) (args : list expr).

Definition special_of (e : expr) : option special := match e with
 | EIf _ _ _ => Some SIf | EAnd _ _ => Some SAnd | EOr _ _ => Some SOr
 | ECond _ => Some SCond | ETrap _ _ => Some STrapError | EDefun _ _ _ => Some SDefun
 | ELam _ _ => Some SLambda | ELet _ _ _ => Some SLet | EFreeze _ => Some SFreeze
 | EType _ => Some SType | _ => None end.
End KLSyntax.
