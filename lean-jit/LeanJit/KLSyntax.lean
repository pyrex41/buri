import LeanJit.Observation
/-! Port of `rocq/KLSyntax.v`: the canonical KLambda surface and resolved syntax. -/
namespace KLSyntax
open Observation

abbrev name := text

def text_eqb : text → text → Bool
  | [], [] => true
  | x :: a, y :: b => (x == y) && text_eqb a b
  | _, _ => false

theorem text_eqb_eq : ∀ a b, text_eqb a b = true ↔ a = b := by
  intro a; induction a with
  | nil => intro b; cases b <;> simp [text_eqb]
  | cons x a ih => intro b; cases b <;> simp [text_eqb, ih]

theorem text_eqb_refl (a : text) : text_eqb a a = true := (text_eqb_eq a a).2 rfl

theorem text_eqb_neq (a b : text) : text_eqb a b = false ↔ a ≠ b := by
  constructor
  · intro H E; subst E; rw [text_eqb_refl] at H; cases H
  · intro H; cases E : text_eqb a b
    · rfl
    · exact absurd ((text_eqb_eq a b).1 E) H

/-- ASCII spelling helper (Rocq: `nat_of_ascii` of each byte of the string). -/
def of_string (s : String) : text := s.toList.map Char.toNat

inductive num | NInt (z : Int) | NFloat (bits : Nat) deriving DecidableEq, Repr

inductive prim
  | PIntern
  | PPos | PTlstr | PCn | PStr | PStringP | PNToString | PStringToN
  | PSet | PValue
  | PSimpleError | PErrorToString
  | PCons | PHd | PTl | PConsP
  | PEqual | PEvalKL
  | PAbsvector | PAddressSet | PAddressGet | PAbsvectorP
  | PWriteByte | PReadByte | POpen | PClose
  | PGetTime
  | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe | PNumberP
  deriving DecidableEq, Repr
open prim

def all_prims : List prim :=
  [PIntern, PPos, PTlstr, PCn, PStr, PStringP, PNToString, PStringToN, PSet, PValue,
   PSimpleError, PErrorToString, PCons, PHd, PTl, PConsP, PEqual, PEvalKL,
   PAbsvector, PAddressSet, PAddressGet, PAbsvectorP, PWriteByte, PReadByte, POpen, PClose,
   PGetTime, PAdd, PSub, PMul, PDiv, PGt, PLt, PGe, PLe, PNumberP]
theorem all_prims_complete : ∀ p, p ∈ all_prims := by
  intro p; cases p <;> simp [all_prims]

def prim_name : prim → String
  | PIntern => "intern" | PPos => "pos" | PTlstr => "tlstr" | PCn => "cn" | PStr => "str"
  | PStringP => "string?" | PNToString => "n->string" | PStringToN => "string->n"
  | PSet => "set" | PValue => "value" | PSimpleError => "simple-error"
  | PErrorToString => "error-to-string" | PCons => "cons" | PHd => "hd" | PTl => "tl"
  | PConsP => "cons?" | PEqual => "=" | PEvalKL => "eval-kl" | PAbsvector => "absvector"
  | PAddressSet => "address->" | PAddressGet => "<-address" | PAbsvectorP => "absvector?"
  | PWriteByte => "write-byte" | PReadByte => "read-byte" | POpen => "open" | PClose => "close"
  | PGetTime => "get-time" | PAdd => "+" | PSub => "-" | PMul => "*" | PDiv => "/"
  | PGt => ">" | PLt => "<" | PGe => ">=" | PLe => "<=" | PNumberP => "number?"

def prim_arity : prim → Nat
  | PIntern | PTlstr | PStr | PStringP | PNToString | PStringToN | PValue | PSimpleError
  | PErrorToString | PHd | PTl | PConsP | PEvalKL | PAbsvector | PAbsvectorP | PReadByte
  | PClose | PGetTime | PNumberP => 1
  | PPos | PCn | PSet | PCons | PEqual | PAddressGet | PWriteByte | POpen
  | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe => 2
  | PAddressSet => 3

inductive special | SIf | SAnd | SOr | SCond | STrapError | SDefun | SLambda | SLet | SFreeze | SType
  deriving DecidableEq, Repr
open special
def all_specials : List special := [SIf, SAnd, SOr, SCond, STrapError, SDefun, SLambda, SLet, SFreeze, SType]
theorem all_specials_complete : ∀ s, s ∈ all_specials := by
  intro s; cases s <;> simp [all_specials]
def special_name : special → String
  | SIf => "if" | SAnd => "and" | SOr => "or" | SCond => "cond" | STrapError => "trap-error"
  | SDefun => "defun" | SLambda => "lambda" | SLet => "let" | SFreeze => "freeze" | SType => "type"

theorem canonical_kl_surface : all_prims.length = 36 ∧ all_specials.length = 10 ∧
    (all_prims.map prim_name ++ all_specials.map special_name).Nodup := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- Resolved KLambda syntax (a nested inductive through `List`, as in Rocq). -/
inductive expr
  | ENum (n : num) | EStr (t : text) | ESym (s : name) | EBool (b : Bool) | ENil
  | EVar (x : name)
  | ELam (x : name) (body : expr)
  | ELet (x : name) (a body : expr)
  | EIf (c a b : expr)
  | EAnd (a b : expr) | EOr (a b : expr)
  | ECond (clauses : List (expr × expr))
  | ETrap (body handler : expr)
  | EFreeze (body : expr)
  | EType (e : expr)
  | EDefun (f : name) (params : List name) (body : expr)
  | EApp (head : expr) (args : List expr)
  | ECall (f : name) (args : List expr)
  deriving Repr
open expr

def special_of : expr → Option special
  | EIf .. => some SIf | EAnd .. => some SAnd | EOr .. => some SOr
  | ECond _ => some SCond | ETrap .. => some STrapError | EDefun .. => some SDefun
  | ELam .. => some SLambda | ELet .. => some SLet | EFreeze _ => some SFreeze
  | EType _ => some SType | _ => none

end KLSyntax
