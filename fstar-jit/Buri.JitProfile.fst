(* Port of rocq/JitProfile.v: the Shen/JIT semantic profile, its port options, and the
   deviation table. *)
module Buri.JitProfile
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.KLPort
module F = Buri.JitFloat
module B = Buri.JitBytecode

let double_of (n : num) : nat = match n with NInt z -> F.of_Z z | NFloat b -> b

let jit_inexact_op (p : prim) (a b : num) : option num =
  let x = double_of a in let y = double_of b in
  match p with
  | PAdd -> Some (NFloat (F.add x y))
  | PSub -> Some (NFloat (F.sub x y))
  | PMul -> Some (NFloat (F.mul x y))
  | PDiv -> if F.is_zero y then None else Some (NFloat (F.div x y))
  | _ -> None

let jit_order (p : prim) (c : option comparison) : bool = match p, c with
  | PGt, Some Gt | PLt, Some Lt | PEqual, Some Eq -> true
  | PGe, Some Gt | PGe, Some Eq | PLe, Some Lt | PLe, Some Eq -> true
  | _, _ -> false
let flip (c : option comparison) : option comparison = match c with
  | Some Lt -> Some Gt | Some Gt -> Some Lt | c -> c
let jit_inexact_cmp (p : prim) (a b : num) : bool =
  match a, b with
  | NInt x, NFloat y -> jit_order p (B.compare_fix_real x y)
  | NFloat x, NInt y -> jit_order p (flip (B.compare_fix_real y x))
  | _, _ -> jit_order p (F.compare (double_of a) (double_of b))

let jit_int_div (x y : int) : num = NFloat (F.div (F.of_Z x) (F.of_Z y))

let jit_str_other (v : value) : option text = match v with
  | VStr s -> Some (app [34] (app s [34]))
  | VNil -> Some (of_string "()")
  | VCons _ _ -> Some (of_string "#<pair>")
  | VVec _ -> Some (of_string "#<absvector>")
  | VStream _ -> Some (of_string "#<stream>")
  | VExn _ -> Some (of_string "#<exception>")
  | VLam _ _ _ | VFrozen _ _ | VPartial _ _ -> Some (of_string "#<procedure>")
  | _ -> None

let jit_sys_message (x : exn) : text = match x with
  | XDivZero -> of_string "division by zero"
  | XCondFail -> of_string "cond: no clause applies"
  | _ -> of_string "error"

let jit_time (_ : text) (z : int) : option num =
  if 0 <= z && z < 18446744073709551616 then Some (NFloat (to_nat z)) else None

let jit_profile : profile = {
  inexact_op = jit_inexact_op; inexact_cmp = jit_inexact_cmp; int_div_inexact = jit_int_div;
  float_text = F.format_real; str_other = jit_str_other; sys_message = jit_sys_message;
  absvector_fill = VSym (of_string "shen.fail!"); time_value = jit_time;
  stack_limit = None; heap_limit = None }

let jit_division_by_zero_real (a b : num)
  : Lemma (requires F.is_zero (double_of b) = true) (ensures jit_inexact_op PDiv a b == None) = ()

let jit_absvector_fill () : Lemma (jit_profile.absvector_fill == VSym (of_string "shen.fail!")) = ()

(* --- The options --- *)
let byte_ok (z : int) : bool = 0 <= z && z <= 255

let is_fixed_name (f : name) : bool =
  existsb (fun (e : string & B.prim & nat) -> match e with (nm, _, _) -> text_eqb f (of_string nm)) B.prim_table
  || keyword f || text_eqb f (of_string "do") || text_eqb f (of_string "thaw") || text_eqb f (of_string "protect")

let jit_rules (sealed : list name) : port_rules = {
  int_range = Some (B.fix_min, B.fix_max);
  char_ok = byte_ok;
  object_identity = true;
  arity_errors = true;
  defun_allowed = (fun _ f -> not (is_fixed_name f || existsb (text_eqb f) sealed));
  time_kind_ok = (fun k -> text_eqb k (of_string "run") || text_eqb k (of_string "unix"));
  unchecked_writes = false;
  resource_exn = (fun r -> match r with
    | RHeap -> Some (XUser (of_string "out of memory"))
    | RStack -> Some (XUser (of_string "stack overflow"))) }

let fix_max_val : int = B.fix_max

let jit_overflow_raises (sealed : list name) (s : store)
  : Lemma (rule_arith_r (jit_rules sealed) jit_profile PAdd zadd [VNum (NInt fix_max_val); VNum (NInt 1)] s == dom PAdd) =
  assert_norm (in_range (jit_rules sealed) (zadd fix_max_val 1) = false);
  range_raises (jit_rules sealed) jit_profile PAdd zadd fix_max_val 1 s

let jit_compare_exact ()
  : Lemma (jit_inexact_cmp PGt (NInt 9007199254740993) (NFloat (F.of_Z 9007199254740992)) = true /\
           jit_inexact_cmp PEqual (NInt 9007199254740993) (NFloat (F.of_Z 9007199254740992)) = false) =
  assert_norm (jit_inexact_cmp PGt (NInt 9007199254740993) (NFloat (F.of_Z 9007199254740992)) = true);
  assert_norm (jit_inexact_cmp PEqual (NInt 9007199254740993) (NFloat (F.of_Z 9007199254740992)) = false)

let jit_byte_strings (sealed : list name) (s : store)
  : Lemma (rule_n_to_string_r (jit_rules sealed) [VNum (NInt 256)] s == dom PNToString /\
           rule_n_to_string_r (jit_rules sealed) [VNum (NInt 255)] s == ret (VStr [255]) s) = ()

let jit_writes_checked (sealed : list name) args s
  : Lemma (rule_write_byte_r (jit_rules sealed) args s == rule_write_byte args s) = ()

let jit_no_partial sealed g args k s ps b
  : Lemma (requires lookup g s.gfuns == Some (FUser ps b) /\ length args <> length ps)
          (ensures call_named_r (jit_rules sealed) jit_profile g args k s == MTau (cfg (Throw XArity) k s)) =
  no_partial_application (jit_rules sealed) jit_profile g args k s ps b

let jit_resources_catchable sealed k s
  : Lemma (next_r (jit_rules sealed) jit_profile (cfg (Fail RStack) k s)
           == MTau (cfg (Throw (XUser (of_string "stack overflow"))) k s)) = ()

let jit_defun_fixed_refused sealed rho ps b k s
  : Lemma (eval_move_r (jit_rules sealed) jit_profile rho (EDefun (of_string "hd") ps b) k s
           == MTau (cfg (Throw XBadDefinition) k s)) =
  assert_norm (is_fixed_name (of_string "hd") = true)

let jit_defun_sealed_refused sealed f rho ps b k s
  : Lemma (requires existsb (text_eqb f) sealed = true)
          (ensures eval_move_r (jit_rules sealed) jit_profile rho (EDefun f ps b) k s
                   == MTau (cfg (Throw XBadDefinition) k s)) = ()

(* --- The deviation table --- *)
type disposition = | In_profile | In_port_rules | In_bytecode | Partly_stated | Ledger_only
type deviation = { d_id : string; d_rule : string; d_where : disposition; d_ledger : string }
let dev a b c d : deviation = { d_id = a; d_rule = b; d_where = c; d_ledger = d }

let deviations : list deviation =
 [dev "fixnum-overflow" "integers are 62-bit; a result out of range raises integer overflow (semantics.md s3)"
    In_port_rules "OB-JIT-DEV-FIXNUM";
  dev "ieee-doubles" "reals are binary64; mixed arithmetic gives a real" In_profile "OB-JIT-FLOAT-MODEL";
  dev "division" "integer division exact or real; any zero divisor raises" In_profile "OB-JIT-DEV-DIVISION";
  dev "mixed-equality" "= and comparisons across integers and reals are exact (s3); #2 fixed at this pin" In_profile "OB-JIT-ISSUE-2";
  dev "nan-identity" "a NaN is = to itself as one object and to nothing else" In_bytecode "OB-JIT-NAN-IDENTITY";
  dev "literals" "reader overrides make out-of-range literals reals (s3)" Ledger_only "OB-JIT-DEV-LITERALS";
  dev "printing" "reals print shortest round-trip digits (s3)" In_profile "OB-JIT-DEV-PRINTING";
  dev "byte-strings" "strings are bytes; n->string takes 0 to 255 (s4)" In_port_rules "OB-JIT-DEV-BYTES";
  dev "hash" "hash is consistent with = and hashes 8 and 8.0 alike (s6)" In_bytecode "OB-JIT-DEV-HASH";
  dev "closure-equality" "closures and streams compare by identity; two exceptions stay undefined here (s6)" Partly_stated "OB-JIT-DEV-IDENTITY";
  dev "error-to-string" "error-to-string of a non-exception raises (s8)" In_bytecode "OB-JIT-DEV-ETS";
  dev "cond-no-clause" "cond with no true clause raises (s9)" In_profile "OB-JIT-DEV-COND";
  dev "no-partial" "a named call of the wrong arity raises; there is no partial application (s9)"
    In_port_rules "OB-JIT-DEV-ARITY";
  dev "symbols-not-procedures" "applying a symbol raises (s9)" In_bytecode "OB-JIT-DEV-APPLY";
  dev "defun-validation" "malformed defun raises at definition (s10)" Ledger_only "OB-JIT-DEV-DEFUN";
  dev "fixed-names" "defun of a fixed name raises (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  dev "sealing" "defun of a sealed name raises; sealed calls bind once (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  dev "lazy-lambda-form" "lambda forms are made on first fn; a placeholder before that (s11)" Ledger_only "OB-JIT-DEV-LAZY-FORM";
  dev "get-time" "get-time takes run and unix only, and returns reals (s12)" In_port_rules "OB-JIT-DEV-TIME";
  dev "char-streams" "char-stream? is false; read-unit-string and write-string raise (s12)" In_bytecode "OB-JIT-DEV-CHAR";
  dev "catchable-resources" "stack overflow and out of memory are catchable errors (s14)"
    In_port_rules "OB-JIT-DEV-RESOURCES";
  dev "cyclic-equality" "= on a cycle, or past its budgets, ends the process; #3's deep-term crash is fixed (s6)" Ledger_only "OB-JIT-ISSUE-3"]
