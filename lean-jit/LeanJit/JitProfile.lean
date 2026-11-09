import LeanJit.KLPort
import LeanJit.JitBytecode3
/-! Port of `rocq/JitProfile.v`: the Shen/JIT semantic profile, port rules and deviation table. -/
namespace JitProfile
open Observation KLSyntax KLSyntax.prim KLSyntax.expr KLValue KLValue.value KLValue.exn
open KLSemantics KLSemantics.control KLSemantics.move KLSemantics.config KLPort

def double_of : num → Nat
  | .NInt z => JitFloat.of_Z z
  | .NFloat b => b

def jit_inexact_op (p : prim) (a b : num) : Option num :=
  let x := double_of a
  let y := double_of b
  match p with
  | PAdd => some (.NFloat (JitFloat.add x y))
  | PSub => some (.NFloat (JitFloat.sub x y))
  | PMul => some (.NFloat (JitFloat.mul x y))
  | PDiv => if JitFloat.is_zero y then none else some (.NFloat (JitFloat.div x y))
  | _ => none

def jit_order (p : prim) (c : Option Ordering) : Bool := match p, c with
  | PGt, some .gt | PLt, some .lt | PEqual, some .eq => true
  | PGe, some .gt | PGe, some .eq | PLe, some .lt | PLe, some .eq => true
  | _, _ => false
def flip (c : Option Ordering) : Option Ordering := match c with
  | some .lt => some .gt | some .gt => some .lt | c => c
def jit_inexact_cmp (p : prim) (a b : num) : Bool :=
  match a, b with
  | .NInt x, .NFloat y => jit_order p (JitBytecode.compare_fix_real x y)
  | .NFloat x, .NInt y => jit_order p (flip (JitBytecode.compare_fix_real y x))
  | _, _ => jit_order p (JitFloat.compare (double_of a) (double_of b))

def jit_int_div (x y : Int) : num := .NFloat (JitFloat.div (JitFloat.of_Z x) (JitFloat.of_Z y))

def jit_str_other (v : value) : Option text := match v with
  | VStr s => some ([34] ++ s ++ [34])
  | VNil => some (of_string "()")
  | VCons _ _ => some (of_string "#<pair>")
  | VVec _ => some (of_string "#<absvector>")
  | VStream _ => some (of_string "#<stream>")
  | VExn _ => some (of_string "#<exception>")
  | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => some (of_string "#<procedure>")
  | _ => none

def jit_sys_message (x : exn) : text := match x with
  | XDivZero => of_string "division by zero"
  | XCondFail => of_string "cond: no clause applies"
  | _ => of_string "error"

def jit_time (_ : text) (z : Int) : Option num :=
  if decide (0 ≤ z) && decide (z < 18446744073709551616) then some (.NFloat z.toNat) else none

def jit_profile : profile :=
  ⟨jit_inexact_op, jit_inexact_cmp, jit_int_div, JitFloat.format_real, jit_str_other, jit_sys_message,
   VSym (of_string "shen.fail!"), jit_time, none, none⟩

theorem jit_division_by_zero_real (a b : num) (H : JitFloat.is_zero (double_of b) = true) :
    jit_inexact_op PDiv a b = none := by
  simp [jit_inexact_op, H]

theorem jit_absvector_fill : jit_profile.absvector_fill = VSym (of_string "shen.fail!") := rfl

-- --- The options ---
def byte_ok (z : Int) : Bool := decide (0 ≤ z) && decide (z ≤ 255)

def is_fixed_name (f : name) : Bool :=
  JitBytecode.prim_table.any (fun e => match e with | (nm, _, _) => text_eqb f (of_string nm))
  || keyword f || text_eqb f (of_string "do") || text_eqb f (of_string "thaw") || text_eqb f (of_string "protect")

def jit_rules (sealed : List name) : port_rules :=
  ⟨some (JitBytecode.fix_min, JitBytecode.fix_max),
   byte_ok,
   true,
   true,
   (fun _ f => !(is_fixed_name f || sealed.any (text_eqb f))),
   (fun k => text_eqb k (of_string "run") || text_eqb k (of_string "unix")),
   false,
   (fun r => match r with
    | .RHeap => some (XUser (of_string "out of memory"))
    | .RStack => some (XUser (of_string "stack overflow")))⟩

def fix_max_val : Int := JitBytecode.fix_max

theorem jit_overflow_raises (sealed : List name) (s : store) :
    rule_arith_r (jit_rules sealed) jit_profile PAdd (· + ·) [VNum (.NInt fix_max_val), VNum (.NInt 1)] s = dom PAdd :=
  range_raises _ _ _ _ _ _ _
    (by show in_range (jit_rules []) (fix_max_val + 1) = false; decide +kernel)

theorem jit_compare_exact :
    jit_inexact_cmp PGt (.NInt 9007199254740993) (.NFloat (JitFloat.of_Z 9007199254740992)) = true ∧
    jit_inexact_cmp PEqual (.NInt 9007199254740993) (.NFloat (JitFloat.of_Z 9007199254740992)) = false := by
  constructor <;> decide +kernel

theorem jit_byte_strings (sealed : List name) (s : store) :
    rule_n_to_string_r (jit_rules sealed) [VNum (.NInt 256)] s = dom PNToString ∧
    rule_n_to_string_r (jit_rules sealed) [VNum (.NInt 255)] s = ret (VStr [255]) s :=
  ⟨rfl, rfl⟩

theorem jit_writes_checked (sealed : List name) (args : List value) (s : store) :
    rule_write_byte_r (jit_rules sealed) args s = rule_write_byte args s := rfl

theorem jit_no_partial (sealed : List name) (g : name) (args : List value) (k : List frame) (s : store)
    (ps : List name) (b : expr) (L : lookup g s.gfuns = some (.FUser ps b)) (N : args.length ≠ ps.length) :
    call_named_r (jit_rules sealed) jit_profile g args k s = MTau (Cfg (Throw XArity) k s) :=
  no_partial_application _ _ _ _ _ _ _ _ rfl L N

theorem jit_resources_catchable (sealed : List name) (k : List frame) (s : store) :
    next_r (jit_rules sealed) jit_profile (Cfg (Fail .RStack) k s)
      = MTau (Cfg (Throw (XUser (of_string "stack overflow"))) k s) :=
  catchable_resource _ _ _ _ _ _ rfl

theorem jit_defun_fixed_refused (sealed : List name) (rho : lenv) (ps : List name) (b : expr)
    (k : List frame) (s : store) :
    eval_move_r (jit_rules sealed) jit_profile rho (EDefun (of_string "hd") ps b) k s
      = MTau (Cfg (Throw XBadDefinition) k s) :=
  defun_refused _ _ _ _ _ _ _ _ (by
    have h : is_fixed_name (of_string "hd") = true := by decide +kernel
    simp only [jit_rules, h, Bool.true_or, Bool.not_true])

theorem jit_defun_sealed_refused (sealed : List name) (f : name) (rho : lenv) (ps : List name) (b : expr)
    (k : List frame) (s : store) (H : sealed.any (text_eqb f) = true) :
    eval_move_r (jit_rules sealed) jit_profile rho (EDefun f ps b) k s
      = MTau (Cfg (Throw XBadDefinition) k s) :=
  defun_refused _ _ _ _ _ _ _ _ (by simp only [jit_rules, H, Bool.or_true, Bool.not_true])

-- --- The deviation table ---
inductive disposition | In_profile | In_port_rules | In_bytecode | Partly_stated | Ledger_only
open disposition
structure deviation where
  Dev ::
  d_id : String
  d_rule : String
  d_where : disposition
  d_ledger : String
open deviation (Dev)

def deviations : List deviation :=
 [Dev "fixnum-overflow" "integers are 62-bit; a result out of range raises integer overflow (semantics.md s3)"
    In_port_rules "OB-JIT-DEV-FIXNUM",
  Dev "ieee-doubles" "reals are binary64; mixed arithmetic gives a real" In_profile "OB-JIT-FLOAT-MODEL",
  Dev "division" "integer division exact or real; any zero divisor raises" In_profile "OB-JIT-DEV-DIVISION",
  Dev "mixed-equality" "= and comparisons across integers and reals are exact (s3); #2 fixed at this pin" In_profile "OB-JIT-ISSUE-2",
  Dev "nan-identity" "a NaN is = to itself as one object and to nothing else" In_bytecode "OB-JIT-NAN-IDENTITY",
  Dev "literals" "reader overrides make out-of-range literals reals (s3)" Ledger_only "OB-JIT-DEV-LITERALS",
  Dev "printing" "reals print shortest round-trip digits (s3)" In_profile "OB-JIT-DEV-PRINTING",
  Dev "byte-strings" "strings are bytes; n->string takes 0 to 255 (s4)" In_port_rules "OB-JIT-DEV-BYTES",
  Dev "hash" "hash is consistent with = and hashes 8 and 8.0 alike (s6)" In_bytecode "OB-JIT-DEV-HASH",
  Dev "closure-equality" "closures and streams compare by identity; two exceptions stay undefined here (s6)" Partly_stated "OB-JIT-DEV-IDENTITY",
  Dev "error-to-string" "error-to-string of a non-exception raises (s8)" In_bytecode "OB-JIT-DEV-ETS",
  Dev "cond-no-clause" "cond with no true clause raises (s9)" In_profile "OB-JIT-DEV-COND",
  Dev "no-partial" "a named call of the wrong arity raises; there is no partial application (s9)"
    In_port_rules "OB-JIT-DEV-ARITY",
  Dev "symbols-not-procedures" "applying a symbol raises (s9)" In_bytecode "OB-JIT-DEV-APPLY",
  Dev "defun-validation" "malformed defun raises at definition (s10)" Ledger_only "OB-JIT-DEV-DEFUN",
  Dev "fixed-names" "defun of a fixed name raises (s10)" In_port_rules "OB-JIT-DEV-SEALING",
  Dev "sealing" "defun of a sealed name raises; sealed calls bind once (s10)" In_port_rules "OB-JIT-DEV-SEALING",
  Dev "lazy-lambda-form" "lambda forms are made on first fn; a placeholder before that (s11)" Ledger_only "OB-JIT-DEV-LAZY-FORM",
  Dev "get-time" "get-time takes run and unix only, and returns reals (s12)" In_port_rules "OB-JIT-DEV-TIME",
  Dev "char-streams" "char-stream? is false; read-unit-string and write-string raise (s12)" In_bytecode "OB-JIT-DEV-CHAR",
  Dev "catchable-resources" "stack overflow and out of memory are catchable errors (s14)"
    In_port_rules "OB-JIT-DEV-RESOURCES",
  Dev "cyclic-equality" "= on a cycle, or past its budgets, ends the process; #3's deep-term crash is fixed (s6)" Ledger_only "OB-JIT-ISSUE-3"]

end JitProfile
