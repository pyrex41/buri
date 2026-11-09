import LeanJit.JitProfile
/-! Port of `rocq/JitLowerRel.v`: what it means for bytecode to be a lowering of a KLambda
expression. Constructor variables are implicit here (explicit in Rocq); the hypotheses and
their order are the same. -/
namespace JitLowerRel
open KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value
abbrev B.code := JitBytecode.code
abbrev B.instr := JitBytecode.instr
abbrev B.val := JitBytecode.val
abbrev B.operand := JitBytecode.operand
open JitBytecode (Pos)

-- ---------- data ----------
inductive VR : value → JitBytecode.val → Prop
  | VR_int z : VR (VNum (.NInt z)) (.VFix z)
  | VR_real b : VR (VNum (.NFloat b)) (.VReal b)
  | VR_sym s : VR (VSym s) (.VSym (JitBytecode.sym_of_text s))
  | VR_bool b : VR (VBool b) (.VBool b)
  | VR_str t : VR (VStr t) (.VStr t)
  | VR_nil : VR VNil .VNil
  | VR_cons a a' d d' : VR a a' → VR d d' → VR (VCons a d) (.VPair a' d')

def lit_val (e : expr) : Option value := match e with
  | ENum n => some (VNum n) | EStr t => some (VStr t) | ESym s => some (VSym s)
  | EBool b => some (VBool b) | ENil => some VNil | _ => none

def pmap (p : prim) : Option JitBytecode.prim := match p with
  | PAdd => some .PAdd | PSub => some .PSub | PMul => some .PMul
  | PGt => some .PGt | PLt => some .PLt | PGe => some .PGe | PLe => some .PLe
  | PCons => some .PCons | PHd => some .PHd | PTl => some .PTl | PConsP => some .PConsp
  | PNumberP => some .PNumberp | PStringP => some .PStringp
  | _ => none

def prim_of_name (f : name) : Option prim :=
  all_prims.find? (fun p => text_eqb f (of_string (prim_name p)))

abbrev env := List (name × Nat)

def slot_is (o : Option Nat) (s : Nat) : Bool := match o with | some x => x == s | none => false
def kill (s : Nat) (e : env) : env := e.filter (fun p => !(slot_is (lookup p.1 e) s))

def bind : List name → Nat → env
  | [], _ => []
  | p :: ps, s => (p, s) :: bind ps (s + 1)

inductive dest | DSlot (d : Nat) | DRet
open dest
def call_instr (i : JitBytecode.instr) (d a : Nat) (f : Pos) (n : Nat) : Prop :=
  i = .ICall d a f n ∨ i = .ICallSealed d a f n
def tail_instr (i : JitBytecode.instr) (a : Nat) (f : Pos) (n : Nat) : Prop :=
  i = .ITail a f n ∨ i = .ITailSealed a f n
def not_prim_name (f : name) : Prop := prim_of_name f = none

section Code
variable (c : JitBytecode.code)
def ins : List JitBytecode.instr := JitBytecode.code_ins c
def konst (k : Nat) : Option JitBytecode.val := (JitBytecode.code_consts c)[k]?
def lbl (l : Nat) : Option (List JitBytecode.instr) := JitBytecode.find_label l (ins c)

mutual
inductive Comp : env → Nat → expr → dest → List JitBytecode.instr → List JitBytecode.instr → Prop
  | C_lit {g top e v v' d k r} : lit_val e = some v → konst c k = some v' → VR v v' →
      Comp g top e (DSlot d) (.IConst d k :: r) r
  | C_move {g top x s d r} : lookup x g = some s → s ≠ d →
      Comp g top (EVar x) (DSlot d) (.IMove d s :: r) r
  | C_same {g top x d r} : lookup x g = some d → Comp g top (EVar x) (DSlot d) r r
  | C_prim {g top f p q args ops d r r'} :
      prim_of_name f = some p → pmap p = some q → args.length = prim_arity p → args ≠ [] →
      CompOps g top args ops r (.IPrim d q ops :: r') → Comp g top (ECall f args) (DSlot d) r r'
  | C_let {g top x a b dst r r1 r'} : Comp g (top + 1) a (DSlot top) r r1 →
      Comp ((x, top) :: g) (top + 1) b dst r1 r' → Comp g top (ELet x a b) dst r r'
  | C_alias {g top x y s b dst r r'} : lookup y g = some s →
      Comp ((x, s) :: g) top b dst r r' → Comp g top (ELet x (EVar y) b) dst r r'
  | C_if_slot {g top t a b d l e0 r r1 r3 r'} : CompT g top t l r r1 →
      Comp g top a (DSlot d) r1 (.IJump e0 :: .ILabel l :: r3) → lbl c l = some r3 →
      Comp g top b (DSlot d) r3 (.ILabel e0 :: r') → lbl c e0 = some r' →
      Comp g top (EIf t a b) (DSlot d) r r'
  | C_if_ret {g top t a b l r r1 r3 r'} : CompT g top t l r r1 →
      Comp g top a DRet r1 (.ILabel l :: r3) → lbl c l = some r3 → Comp g top b DRet r3 r' →
      Comp g top (EIf t a b) DRet r r'
  | C_cond_nil {g top d r} : Comp g top (ECond []) (DSlot d) (.IPrim d .PRaiseCond [] :: r) r
  | C_cond_true {g top x rest dst r r'} : Comp g top x dst r r' →
      Comp g top (ECond ((EBool true, x) :: rest)) dst r r'
  | C_cond_slot {g top t a rest d l e0 r r1 r3 r'} : CompT g top t l r r1 →
      Comp g top a (DSlot d) r1 (.IJump e0 :: .ILabel l :: r3) → lbl c l = some r3 →
      Comp g top (ECond rest) (DSlot d) r3 (.ILabel e0 :: r') → lbl c e0 = some r' →
      Comp g top (ECond ((t, a) :: rest)) (DSlot d) r r'
  | C_cond_ret {g top t a rest l r r1 r3 r'} : CompT g top t l r r1 →
      Comp g top a DRet r1 (.ILabel l :: r3) → lbl c l = some r3 → Comp g top (ECond rest) DRet r3 r' →
      Comp g top (ECond ((t, a) :: rest)) DRet r r'
  | C_type {g top e dst r r'} : Comp g top e dst r r' → Comp g top (EType e) dst r r'
  | C_and {g top x y d l e0 kt kf r r1 r'} : CompT g top x l r r1 →
      CompT g top y l r1 (.IConst d kt :: .IJump e0 :: .ILabel l :: .IConst d kf :: .ILabel e0 :: r') →
      konst c kt = some (.VBool true) → konst c kf = some (.VBool false) →
      lbl c l = some (.IConst d kf :: .ILabel e0 :: r') → lbl c e0 = some r' →
      Comp g top (EAnd x y) (DSlot d) r r'
  | C_or {g top x y d l nx th e0 kt kf r r2 r'} : CompT g top x nx r (.IJump th :: .ILabel nx :: r2) →
      lbl c nx = some r2 →
      CompT g top y l r2 (.ILabel th :: .IConst d kt :: .IJump e0 :: .ILabel l :: .IConst d kf :: .ILabel e0 :: r') →
      lbl c th = some (.IConst d kt :: .IJump e0 :: .ILabel l :: .IConst d kf :: .ILabel e0 :: r') →
      konst c kt = some (.VBool true) → konst c kf = some (.VBool false) →
      lbl c l = some (.IConst d kf :: .ILabel e0 :: r') → lbl c e0 = some r' →
      Comp g top (EOr x y) (DSlot d) r r'
  | C_ret {g top e o top2 r r'} : CompOp g top e o top2 r (.IReturn o :: r') → Comp g top e DRet r r'
  | C_call {g top f args d n i r r'} : not_prim_name f → n = args.length →
      CompW g (top + 2) args r (i :: r') → call_instr i d top (JitBytecode.sym_of_text f) n →
      Comp g top (ECall f args) (DSlot d) r r'
  | C_tail {g top f args n t i r r'} : not_prim_name f → n = args.length →
      n + 2 ≤ t → top ≤ t → CompTA g 2 t args [] r (i :: r') →
      tail_instr i 0 (JitBytecode.sym_of_text f) n →
      Comp g top (ECall f args) DRet r r'
  | C_chain {g top f a e v v' k d r r'} : prim_of_name f = some PCons →
      lit_val a = some v → konst c k = some v' → VR v v' →
      Comp g top e (DSlot d) r (.IPrim d .PCons [.OConst k, .OSlot d] :: r') →
      Comp g top (ECall f [a, e]) (DSlot d) r r'

inductive CompT : env → Nat → expr → Nat → List JitBytecode.instr → List JitBytecode.instr → Prop
  | T_leaf {g top e o top2 l r r'} : CompOp g top e o top2 r (.IJumpIfFalse o l :: r') → CompT g top e l r r'
  | T_and {g top x y l r r1 r'} : CompT g top x l r r1 → CompT g top y l r1 r' → CompT g top (EAnd x y) l r r'
  | T_or {g top x y l nx th r r2 r'} : CompT g top x nx r (.IJump th :: .ILabel nx :: r2) →
      lbl c nx = some r2 → CompT g top y l r2 (.ILabel th :: r') → lbl c th = some r' →
      CompT g top (EOr x y) l r r'
  | T_let {g top x a b l r r1 r'} : Comp g (top + 1) a (DSlot top) r r1 →
      CompT ((x, top) :: g) (top + 1) b l r1 r' → CompT g top (ELet x a b) l r r'
  | T_alias {g top x y s b l r r'} : lookup y g = some s →
      CompT ((x, s) :: g) top b l r r' → CompT g top (ELet x (EVar y) b) l r r'
  | T_type {g top e l r r'} : CompT g top e l r r' → CompT g top (EType e) l r r'

inductive CompOp : env → Nat → expr → JitBytecode.operand → Nat → List JitBytecode.instr → List JitBytecode.instr → Prop
  | O_var {g top x s r} : lookup x g = some s → s < top → CompOp g top (EVar x) (.OSlot s) top r r
  | O_lit {g top e v v' k r} : lit_val e = some v → konst c k = some v' → VR v v' →
      CompOp g top e (.OConst k) top r r
  | O_val {g top e r r'} : Comp g (top + 1) e (DSlot top) r r' →
      CompOp g top e (.OSlot top) (top + 1) r r'
  | O_type {g top e o top2 r r'} : CompOp g top e o top2 r r' → CompOp g top (EType e) o top2 r r'

inductive CompOps : env → Nat → List expr → List JitBytecode.operand → List JitBytecode.instr → List JitBytecode.instr → Prop
  | Os_nil {g top r} : CompOps g top [] [] r r
  | Os_cons {g top e es o os top2 r r1 r'} : CompOp g top e o top2 r r1 →
      CompOps g top2 es os r1 r' → CompOps g top (e :: es) (o :: os) r r'

inductive CompW : env → Nat → List expr → List JitBytecode.instr → List JitBytecode.instr → Prop
  | W_nil {g s r} : CompW g s [] r r
  | W_cons {g s e es r r1 r'} : Comp g (s + 1) e (DSlot s) r r1 → CompW g (s + 1) es r1 r' →
      CompW g s (e :: es) r r'

inductive CompTA : env → Nat → Nat → List expr → List (Nat × Nat) → List JitBytecode.instr → List JitBytecode.instr → Prop
  | TA_nil {g s t ms r'} : CompTA g s t [] ms (ms.map (fun m => JitBytecode.instr.IMove m.1 m.2) ++ r') r'
  | TA_same {g s t x es ms r r'} : lookup x g = some s → CompTA g (s + 1) t es ms r r' →
      CompTA g s t (EVar x :: es) ms r r'
  | TA_temp {g s t e es ms r r1 r'} : Comp g (t + 1) e (DSlot t) r r1 →
      CompTA g (s + 1) (t + 1) es ((s, t) :: ms) r1 r' → CompTA g s t (e :: es) ms r r'
  | TA_direct {g s t e es ms r r1 r'} : Comp g t e (DSlot s) r r1 →
      CompTA (kill s g) (s + 1) t es ms r1 r' → CompTA g s t (e :: es) ms r r'
end
end Code

def CompFn (c : JitBytecode.code) (ps : List name) (b : expr) : Prop :=
  ∃ r', Comp c (bind ps 2) (2 + ps.length) b DRet (JitBytecode.code_ins c) r'

end JitLowerRel
