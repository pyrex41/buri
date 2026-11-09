import LeanJit.JitLowerCheck
/-! Port of `rocq/JitLowerStage0.v`: translation validation of stage 0 output. -/
namespace JitLowerStage0
open KLSyntax KLSyntax.expr KLValue KLValue.value KLSemantics JitLowerRel JitLowerCheck

inductive sx | XSym (s : String) | XInt (z : Int) | XReal (b : Nat) | XStr (t : List Nat) | XList (l : List sx)
open sx

mutual
def to_value : sx → value
  | XSym s => if s == "true" then VBool true else if s == "false" then VBool false else VSym (of_string s)
  | XInt z => VNum (.NInt z) | XReal b => VNum (.NFloat b) | XStr t => VStr t
  | XList l => to_value_list l
def to_value_list : List sx → value
  | [] => VNil | a :: d => VCons (to_value a) (to_value_list d)
end
mutual
def to_val : sx → JitBytecode.val
  | XSym s => if s == "true" then .VBool true else if s == "false" then .VBool false
              else .VSym (JitBytecode.sym s)
  | XInt z => .VFix z | XReal b => .VReal b | XStr t => .VStr t
  | XList l => to_val_list l
def to_val_list : List sx → JitBytecode.val
  | [] => .VNil | a :: d => .VPair (to_val a) (to_val_list d)
end

inductive verdict | Accepted (f : name) | Rejected (f : name) | Unparsed
open verdict

def judge (form sbc : sx) : verdict :=
  match parse [] (to_value form), to_val sbc with
  | some (EDefun f ps b), .VPair (.VSym _) (.VPair (.VSym g) (.VPair code .VNil)) =>
    if !((JitBytecode.sym_of_text f).eqb g) then Unparsed else
    match JitBytecode.build_code JitBytecode.prim_tree 64 code with
    | .LOk c =>
      if JitBytecode.code_arity c == ps.length
         && (match JitBytecode.code_entry c with | none => true | some _ => false)
         && check_fn c ps b
      then Accepted f else Rejected f
    | .LErr _ => Rejected f
  | _, _ => Unparsed

def judge_all : List sx → List sx → List verdict
  | f :: fs, s :: ss => judge f s :: judge_all fs ss
  | [], [] => []
  | _, _ => [Unparsed]

def tally (fs ss : List sx) : Nat × Nat × Nat × List name :=
  (judge_all fs ss).foldr (fun v acc => let (a, r, u, names) := acc
    match v with
    | Accepted f => (a + 1, r, u, f :: names)
    | Rejected _ => (a, r + 1, u, names)
    | Unparsed => (a, r, u + 1, names)) (0, 0, 0, [])

/-- The counts only, as stage0-accepted.txt records them. -/
def counts (fs ss : List sx) : Nat × Nat × Nat := let (a, r, u, _) := tally fs ss; (a, r, u)

end JitLowerStage0
