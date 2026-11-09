import LeanJit.KLSyntax
/-! Port of `rocq/KLValue.v`: values, store and semantic profile. -/
namespace KLValue
open Observation KLSyntax KLSyntax.prim

inductive exn
  | XUser (msg : text)
  | XUnboundVar (x : name)
  | XUnboundGlobal (x : name)
  | XUndefinedFun (f : name)
  | XNotCallable | XNotBoolean | XArity
  | XPrim (p : prim)
  | XDivZero | XBounds | XCondFail
  | XBadDefinition
  | XIO (e : io_error)
  | XEvalKL
  deriving DecidableEq, Repr

/-- Values: a nested inductive through `List (name × value)` and `List value`. -/
inductive value
  | VNum (n : num) | VSym (s : name) | VBool (b : Bool) | VStr (t : text) | VNil
  | VCons (a d : value)
  | VVec (l : Nat)
  | VStream (h : Nat)
  | VLam (x : name) (body : expr) (env : List (name × value))
  | VFrozen (body : expr) (env : List (name × value))
  | VPartial (f : name) (args : List value)
  | VExn (x : exn)
  deriving Repr
open value
abbrev lenv := List (name × value)

inductive fundef | FPrim (p : prim) | FUser (params : List name) (body : expr)
def fun_arity : fundef → Nat
  | .FPrim p => prim_arity p
  | .FUser ps _ => ps.length

structure store where
  heap : List (List value)
  gvals : List (name × value)
  gfuns : List (name × fundef)

def lookup {A} (x : name) : List (name × A) → Option A
  | [] => none
  | (y, v) :: l => if text_eqb x y then some v else lookup x l

structure profile where
  inexact_op : prim → num → num → Option num
  inexact_cmp : prim → num → num → Bool
  int_div_inexact : Int → Int → num
  float_text : Nat → text
  str_other : value → Option text
  sys_message : exn → text
  absvector_fill : value
  time_value : text → Int → Option num
  stack_limit : Option Nat
  heap_limit : Option Nat

def int_or (P : profile) (p : prim) (iop : Int → Int → Int) (a b : num) : Option num :=
  match a, b with
  | .NInt x, .NInt y => some (.NInt (iop x y))
  | _, _ => P.inexact_op p a b

/-- Rocq `Z.quot`/`Z.rem` are truncating: Lean `Int.tdiv`/`Int.tmod`. -/
def num_div (P : profile) (a b : num) : Option (Option num) :=
  match a, b with
  | _, .NInt 0 => none
  | .NInt x, .NInt y => some (some (if Int.tmod x y == 0 then .NInt (Int.tdiv x y) else P.int_div_inexact x y))
  | _, _ => some (P.inexact_op PDiv a b)

def num_cmp (P : profile) (p : prim) (a b : num) : Bool :=
  match a, b with
  | .NInt x, .NInt y => match p with
    | PGt => decide (x > y) | PLt => decide (x < y) | PGe => decide (x ≥ y) | PLe => decide (x ≤ y)
    | _ => x == y
  | _, _ => P.inexact_cmp p a b

def list_eq (f : value → value → Option Bool) : List value → List value → Option Bool
  | [], [] => some true
  | x :: xs, y :: ys => match f x y with
    | some true => list_eq f xs ys
    | r => r
  | _, _ => some false

def is_opaque : value → Bool
  | VLam .. | VFrozen .. | VPartial .. | VExn _ => true
  | _ => false

/-- The inner `fix go` of `eq_depth`, with the deeper call `rec` passed in. The Rocq match on
opaque values is a two-level match; `is_opaque` spells the same case split. -/
def eq_go (P : profile) (h : List (List value)) (rec : value → value → Option Bool) :
    value → value → Option Bool
  | VNum x, VNum y => some (num_cmp P PEqual x y)
  | VSym x, VSym y => some (text_eqb x y)
  | VStr x, VStr y => some (text_eqb x y)
  | VBool x, VBool y => some (x == y)
  | VNil, VNil => some true
  | VCons a1 a2, VCons b1 b2 => match eq_go P h rec a1 b1 with
    | some true => eq_go P h rec a2 b2
    | r => r
  | VStream x, VStream y => some (x == y)
  | VVec l1, VVec l2 => if l1 == l2 then some true else
      match h[l1]?, h[l2]? with
      | some xs, some ys => list_eq rec xs ys
      | _, _ => none
  | a, b => if is_opaque a then (if is_opaque b then none else some false) else some false

def eq_depth (P : profile) (h : List (List value)) : Nat → value → value → Option Bool
  | 0 => fun _ _ => none
  | d + 1 => eq_go P h (eq_depth P h d)

def kl_eq (P : profile) (h : List (List value)) (a b : value) : Option Bool :=
  eq_depth P h (h.length + 1) a b

/-- Rocq: `NilZero.string_of_int (Z.to_int z)`, the decimal spelling. -/
def dec_text (z : Int) : text := of_string (toString z)
def bool_text (b : Bool) : text := of_string (if b then "true" else "false")

def scalar_ok (z : Int) : Bool :=
  decide (0 ≤ z) && decide (z ≤ 1114111) && !(decide (55296 ≤ z) && decide (z ≤ 57343))

def heap_cells (h : List (List value)) : Nat := h.foldr (fun v n => v.length + n) 0
def alloc_ok (P : profile) (h : List (List value)) (n : Nat) : Bool :=
  match P.heap_limit with
  | none => true
  | some m => decide (heap_cells h + n + 1 ≤ m)

def replace_nth {A} : Nat → A → List A → List A
  | 0, x, _ :: l => x :: l
  | n + 1, x, y :: l => y :: replace_nth n x l
  | _, _, [] => []
theorem replace_nth_length {A} : ∀ n (x : A) l, (replace_nth n x l).length = l.length := by
  intro n; induction n with
  | zero => intro x l; cases l <;> rfl
  | succ n ih => intro x l; cases l <;> simp [replace_nth, ih]

/- Well-formed values. Rocq writes the environment and argument cases with `fold_right`
inside one `Fixpoint`; Lean's structural recursion needs the folds as mutual functions,
which `fold_lok`/`fold_eok` below relate to `Forall`. -/
mutual
def vok (n : Nat) : value → Prop
  | VCons a d => vok n a ∧ vok n d
  | VVec l => l < n
  | VLam _ _ rho => vok_env n rho
  | VFrozen _ rho => vok_env n rho
  | VPartial _ args => vok_list n args
  | _ => True
def vok_env (n : Nat) : List (name × value) → Prop
  | [] => True
  | (_, w) :: r => vok n w ∧ vok_env n r
def vok_list (n : Nat) : List value → Prop
  | [] => True
  | w :: r => vok n w ∧ vok_list n r
end

def lok (n : Nat) (l : List value) : Prop := ∀ v ∈ l, vok n v
def eok (n : Nat) (rho : lenv) : Prop := ∀ p ∈ rho, vok n p.2

theorem fold_lok (n : Nat) : ∀ l, vok_list n l ↔ lok n l := by
  intro l; induction l with
  | nil => simp [vok_list, lok]
  | cons a l ih => simp [vok_list, lok, ih]
theorem fold_eok (n : Nat) : ∀ rho, vok_env n rho ↔ eok n rho := by
  intro rho; induction rho with
  | nil => simp [vok_env, eok]
  | cons p r ih => obtain ⟨x, w⟩ := p; simp [vok_env, eok, ih]

mutual
theorem vok_mono : ∀ (v : value) {n m : Nat}, n ≤ m → vok n v → vok m v
  | VCons a d, _, _, L, K => by
      simp only [vok] at *; exact ⟨vok_mono a L K.1, vok_mono d L K.2⟩
  | VVec l, _, _, L, K => by simp only [vok] at *; omega
  | VLam _ _ rho, _, _, L, K => by simp only [vok] at *; exact vok_env_mono rho L K
  | VFrozen _ rho, _, _, L, K => by simp only [vok] at *; exact vok_env_mono rho L K
  | VPartial _ args, _, _, L, K => by simp only [vok] at *; exact vok_list_mono args L K
  | VNum _, _, _, _, _ => by simp [vok]
  | VSym _, _, _, _, _ => by simp [vok]
  | VBool _, _, _, _, _ => by simp [vok]
  | VStr _, _, _, _, _ => by simp [vok]
  | VNil, _, _, _, _ => by simp [vok]
  | VStream _, _, _, _, _ => by simp [vok]
  | VExn _, _, _, _, _ => by simp [vok]
theorem vok_env_mono : ∀ (rho : List (name × value)) {n m : Nat}, n ≤ m → vok_env n rho → vok_env m rho
  | [], _, _, _, _ => by simp [vok_env]
  | (_, w) :: r, _, _, L, K => by
      simp only [vok_env] at *; exact ⟨vok_mono w L K.1, vok_env_mono r L K.2⟩
theorem vok_list_mono : ∀ (l : List value) {n m : Nat}, n ≤ m → vok_list n l → vok_list m l
  | [], _, _, _, _ => by simp [vok_list]
  | w :: r, _, _, L, K => by
      simp only [vok_list] at *; exact ⟨vok_mono w L K.1, vok_list_mono r L K.2⟩
end

theorem lok_mono {n m : Nat} {l : List value} (L : n ≤ m) (H : lok n l) : lok m l :=
  fun v I => vok_mono v L (H v I)
theorem eok_mono {n m : Nat} {l : lenv} (L : n ≤ m) (H : eok n l) : eok m l :=
  fun p I => vok_mono p.2 L (H p I)

theorem lookup_ok (n : Nat) (x : name) : ∀ (rho : lenv) (v : value),
    eok n rho → lookup x rho = some v → vok n v := by
  intro rho; induction rho with
  | nil => intro v _ E; cases E
  | cons p rho ih =>
    obtain ⟨y, w⟩ := p; intro v H E
    simp only [lookup] at E
    split at E
    · cases E; exact H (y, w) (by simp)
    · exact ih v (fun q I => H q (by simp [I])) E

def store_ok (s : store) : Prop :=
  (∀ l ∈ s.heap, lok s.heap.length l) ∧ eok s.heap.length s.gvals

end KLValue
