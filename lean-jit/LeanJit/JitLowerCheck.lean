import LeanJit.JitLowerRel
/-! Port of `rocq/JitLowerCheck.v`, the definitions: a checker deciding `Comp` on one code
object. The soundness proof is in `JitLowerCheckSound.lean`. -/
namespace JitLowerCheck
open KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value JitLowerRel JitLowerRel.dest
open JitBytecode (Pos)

def vrb : value → JitBytecode.val → Bool
  | VNum (.NInt z), .VFix y => z == y
  | VNum (.NFloat b), .VReal c => b == c
  | VSym s, .VSym p => (JitBytecode.sym_of_text s).eqb p
  | VBool b, .VBool c => b == c
  | VStr t, .VStr u => text_eqb t u && t.length == u.length
  | VNil, .VNil => true
  | VCons a d, .VPair a' d' => vrb a a' && vrb d d'
  | _, _ => false

def find_k : List JitBytecode.val → value → Nat → Option Nat
  | [], _, _ => none
  | w :: cs, v, i => if vrb v w then some i else find_k cs v (i + 1)

def o_eqb (a b : JitBytecode.operand) : Bool := match a, b with
  | .OSlot x, .OSlot y => x == y | .OConst x, .OConst y => x == y | _, _ => false
def os_eqb : List JitBytecode.operand → List JitBytecode.operand → Bool
  | [], [] => true | x :: a, y :: b => o_eqb x y && os_eqb a b | _, _ => false
def q_eqb (a b : JitBytecode.prim) : Bool := match a, b with
  | .PAdd, .PAdd | .PSub, .PSub | .PMul, .PMul | .PGt, .PGt | .PLt, .PLt | .PGe, .PGe
  | .PLe, .PLe | .PCons, .PCons | .PHd, .PHd | .PTl, .PTl | .PConsp, .PConsp
  | .PNumberp, .PNumberp | .PStringp, .PStringp | .PRaiseCond, .PRaiseCond => true
  | _, _ => false
def is_bool (w : Option JitBytecode.val) (b : Bool) : Bool := match w with
  | some (.VBool c) => b == c | _ => false

mutual
def vars : expr → List name
  | EVar x => [x]
  | ELet _ a b | EAnd a b | EOr a b | ETrap a b => vars a ++ vars b
  | EIf c a b => vars c ++ vars a ++ vars b
  | ECond cl => vars_clauses cl
  | EType a | ELam _ a | EFreeze a | EDefun _ _ a => vars a
  | EApp h args => vars h ++ vars_list args
  | ECall _ args => vars_list args
  | _ => []
def vars_clauses : List (expr × expr) → List name
  | [] => [] | (c, b) :: l => vars c ++ vars b ++ vars_clauses l
def vars_list : List expr → List name
  | [] => [] | a :: l => vars a ++ vars_list l
end
def reads (g : env) (es : List expr) (s : Nat) : Bool :=
  (es.flatMap vars).any (fun x => slot_is (lookup x g) s)

def is_tailcall (i : JitBytecode.instr) (f : Pos) (n : Nat) : Bool := match i with
  | .ITail a f' n' | .ITailSealed a f' n' => a == 0 && f.eqb f' && n == n' | _ => false
def is_call (i : JitBytecode.instr) (d a : Nat) (f : Pos) (n : Nat) : Bool := match i with
  | .ICall d' a' f' n' | .ICallSealed d' a' f' n' => d == d' && a == a' && f.eqb f' && n == n'
  | _ => false

def moves_prefix : List (Nat × Nat) → List JitBytecode.instr → Option (List JitBytecode.instr)
  | [], r => some r
  | (s, t) :: ms, .IMove d u :: r => if s == d && t == u then moves_prefix ms r else none
  | _, _ => none

section Check
variable (c : JitBytecode.code)

def lbl_ok (l : Nat) (r : List JitBytecode.instr) : Bool := match lbl c l with
  | some r' => r'.length == r.length | none => false

def chain_head (d : Nat) (p : prim) (args : List expr) : Option (value × expr) :=
  if 2 + JitBytecode.code_arity c ≤ d then match p, args with
    | PCons, [a, ECall f2 a2] => match lit_val a, prim_of_name f2 with
      | some v, some PCons => some (v, ECall f2 a2) | _, _ => none
    | _, _ => none
  else none
def konst_vr (v : value) (k : Nat) : Bool := match konst c k with | some w => vrb v w | none => false
def chain_tail (d : Nat) (v : value) (r : List JitBytecode.instr) : Option (List JitBytecode.instr) :=
  match r with
  | .IPrim d' q [.OConst k, .OSlot d2] :: r' =>
    if d == d' && d == d2 && q_eqb .PCons q && konst_vr c v k then some r' else none
  | _ => none

mutual
def chk : Nat → env → Nat → expr → dest → List JitBytecode.instr → Option (List JitBytecode.instr)
  | 0, _, _, _, _, _ => none
  | n + 1, g, top, e, dst, r =>
  match e with
  | EType a => chk n g top a dst r
  | ELet x a b => match a with
    | EVar y => match lookup y g with
      | some s => chk n ((x, s) :: g) top b dst r
      | none => match chk n g (top + 1) a (DSlot top) r with
        | some r1 => chk n ((x, top) :: g) (top + 1) b dst r1 | none => none
    | _ => match chk n g (top + 1) a (DSlot top) r with
      | some r1 => chk n ((x, top) :: g) (top + 1) b dst r1 | none => none
  | EIf t a b => match chkT n g top t r with
    | none => none
    | some (l, r1) => match dst with
      | DSlot _ => match chk n g top a dst r1 with
        | some (.IJump e0 :: .ILabel l' :: r3) =>
          if l == l' && lbl_ok c l r3 then match chk n g top b dst r3 with
            | some (.ILabel e0' :: r') => if e0 == e0' && lbl_ok c e0 r' then some r' else none
            | _ => none else none
        | _ => none
      | DRet => match chk n g top a dst r1 with
        | some (.ILabel l' :: r3) => if l == l' && lbl_ok c l r3 then chk n g top b dst r3 else none
        | _ => none
  | ECond [] => match dst, r with
    | DSlot d, .IPrim d' q [] :: r' => if d == d' && q_eqb .PRaiseCond q then some r' else none
    | DRet, _ => match chkOp n g top e r with
      | some (o, _, .IReturn o' :: r') => if o_eqb o o' then some r' else none | _ => none
    | _, _ => none
  | ECond ((EBool true, x) :: _) => chk n g top x dst r
  | ECond ((t, a) :: rest) => match chkT n g top t r with
    | none => none
    | some (l, r1) => match dst with
      | DSlot _ => match chk n g top a dst r1 with
        | some (.IJump e0 :: .ILabel l' :: r3) =>
          if l == l' && lbl_ok c l r3 then match chk n g top (ECond rest) dst r3 with
            | some (.ILabel e0' :: r') => if e0 == e0' && lbl_ok c e0 r' then some r' else none
            | _ => none else none
        | _ => none
      | DRet => match chk n g top a dst r1 with
        | some (.ILabel l' :: r3) => if l == l' && lbl_ok c l r3 then chk n g top (ECond rest) dst r3 else none
        | _ => none
  | ECall f args => match prim_of_name f with
    | some p => match pmap p, dst with
      | some q, DSlot d => match chain_head c d p args with
        | some (v, e2) => match chk n g top e2 (DSlot d) r with
          | some r1 => chain_tail c d v r1 | none => none
        | none =>
          if args.length == prim_arity p && !(args.length == 0) then
            match chkOps n g top args r with
            | some (ops, .IPrim d' q' ops' :: r') =>
              if d == d' && q_eqb q q' && os_eqb ops ops' then some r' else none
            | _ => none
          else none
      | some _, DRet => match chkOp n g top e r with
        | some (o, _, .IReturn o' :: r') => if o_eqb o o' then some r' else none | _ => none
      | none, _ => none
    | none => let k := args.length
      match dst with
      | DSlot d => match chkW n g (top + 2) args r with
        | some (i :: r') => if is_call i d top (JitBytecode.sym_of_text f) k then some r' else none
        | _ => none
      | DRet => let t := max top (k + 2)
        match chkTA n g 2 t args [] r with
        | some (i :: r') => if is_tailcall i (JitBytecode.sym_of_text f) k then some r' else none
        | _ => none
  | _ => match dst with
    | DRet => match chkOp n g top e r with
      | some (o, _, .IReturn o' :: r') => if o_eqb o o' then some r' else none | _ => none
    | DSlot d => match e with
      | EVar x => match lookup x g with
        | some s => if s == d then some r else match r with
          | .IMove d' s' :: r' => if d == d' && s == s' then some r' else none | _ => none
        | none => none
      | EAnd x y => match chkT n g top x r with
        | some (l1, r1) => match chkT n g top y r1 with
          | some (l, .IConst d1 kt :: .IJump e0 :: .ILabel l' :: .IConst d2 kf :: .ILabel e0' :: r') =>
            if l1 == l && d == d1 && d == d2 && l == l' && e0 == e0' && is_bool (konst c kt) true
               && is_bool (konst c kf) false && lbl_ok c l (.IConst d2 kf :: .ILabel e0' :: r') && lbl_ok c e0 r'
            then some r' else none
          | _ => none
        | none => none
      | EOr x y => match chkT n g top x r with
        | some (nx, .IJump th :: .ILabel nx' :: r2) =>
          if nx == nx' && lbl_ok c nx r2 then match chkT n g top y r2 with
            | some (l, .ILabel th' :: .IConst d1 kt :: .IJump e0 :: .ILabel l' :: .IConst d2 kf :: .ILabel e0' :: r') =>
              if th == th' && d == d1 && d == d2 && l == l' && e0 == e0' && is_bool (konst c kt) true
                 && is_bool (konst c kf) false && lbl_ok c th (.IConst d1 kt :: .IJump e0 :: .ILabel l' :: .IConst d2 kf :: .ILabel e0' :: r')
                 && lbl_ok c l (.IConst d2 kf :: .ILabel e0' :: r') && lbl_ok c e0 r'
              then some r' else none
            | _ => none else none
        | _ => none
      | _ => match lit_val e, r with
        | some v, .IConst d' k :: r' => match konst c k with
          | some w => if d == d' && vrb v w then some r' else none | none => none
        | _, _ => none

def chkT : Nat → env → Nat → expr → List JitBytecode.instr → Option (Nat × List JitBytecode.instr)
  | 0, _, _, _, _ => none
  | n + 1, g, top, e, r =>
  match e with
  | EType a => chkT n g top a r
  | EAnd x y => match chkT n g top x r with
    | some (l1, r1) => match chkT n g top y r1 with
      | some (l2, r2) => if l1 == l2 then some (l2, r2) else none | none => none
    | none => none
  | EOr x y => match chkT n g top x r with
    | some (nx, .IJump th :: .ILabel nx' :: r2) =>
      if nx == nx' && lbl_ok c nx r2 then match chkT n g top y r2 with
        | some (l, .ILabel th' :: r') => if th == th' && lbl_ok c th r' then some (l, r') else none
        | _ => none else none
    | _ => none
  | ELet x a b => match a with
    | EVar y => match lookup y g with
      | some s => chkT n ((x, s) :: g) top b r
      | none => match chk n g (top + 1) a (DSlot top) r with
        | some r1 => chkT n ((x, top) :: g) (top + 1) b r1 | none => none
    | _ => match chk n g (top + 1) a (DSlot top) r with
      | some r1 => chkT n ((x, top) :: g) (top + 1) b r1 | none => none
  | _ => match chkOp n g top e r with
    | some (o, _, .IJumpIfFalse o' l :: r') => if o_eqb o o' then some (l, r') else none
    | _ => none

def chkOp : Nat → env → Nat → expr → List JitBytecode.instr → Option (JitBytecode.operand × Nat × List JitBytecode.instr)
  | 0, _, _, _, _ => none
  | n + 1, g, top, e, r =>
  match e with
  | EType a => chkOp n g top a r
  | EVar x => match lookup x g with
    | some s => if s < top then some (.OSlot s, top, r) else none
    | none => none
  | _ => match lit_val e with
    | some v => match find_k (JitBytecode.code_consts c) v 0 with
      | some k => some (.OConst k, top, r) | none => none
    | none => match chk n g (top + 1) e (DSlot top) r with
      | some r1 => some (.OSlot top, top + 1, r1) | none => none

def chkOps : Nat → env → Nat → List expr → List JitBytecode.instr → Option (List JitBytecode.operand × List JitBytecode.instr)
  | 0, _, _, _, _ => none
  | n + 1, g, top, es, r =>
  match es with
  | [] => some ([], r)
  | e :: es => match chkOp n g top e r with
    | some (o, top2, r1) => match chkOps n g top2 es r1 with
      | some (os, r') => some (o :: os, r') | none => none
    | none => none

def chkW : Nat → env → Nat → List expr → List JitBytecode.instr → Option (List JitBytecode.instr)
  | 0, _, _, _, _ => none
  | n + 1, g, s, es, r =>
  match es with
  | [] => some r
  | e :: es => match chk n g (s + 1) e (DSlot s) r with
    | some r1 => chkW n g (s + 1) es r1 | none => none

def chkTA : Nat → env → Nat → Nat → List expr → List (Nat × Nat) → List JitBytecode.instr → Option (List JitBytecode.instr)
  | 0, _, _, _, _, _, _ => none
  | n + 1, g, s, t, es, ms, r =>
  match es with
  | [] => moves_prefix ms r
  | e :: es =>
    let other (_ : Unit) :=
      if reads g es s then match chk n g (t + 1) e (DSlot t) r with
        | some r1 => chkTA n g (s + 1) (t + 1) es ((s, t) :: ms) r1 | none => none
      else match chk n g t e (DSlot s) r with
        | some r1 => chkTA n (kill s g) (s + 1) t es ms r1 | none => none
    match e with
    | EVar x => match lookup x g with
      | some u => if u == s then chkTA n g (s + 1) t es ms r else other ()
      | none => other ()
    | _ => other ()
end
end Check

def fuel : Nat := 4096
def check_fn (c : JitBytecode.code) (ps : List name) (b : expr) : Bool :=
  match chk c fuel (bind ps 2) (2 + ps.length) b DRet (JitBytecode.code_ins c) with
  | some _ => true | none => false

end JitLowerCheck
