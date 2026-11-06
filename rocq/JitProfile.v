(* Shen/JIT Phase 1: the Shen/JIT semantic profile, in the slots of KLValue.profile, its
   options in KLPort.port_rules, and the table of where each deviation is stated. Stating them
   does not show the port refines the semantics under them: that is Phase 2 onward. *)
From Coq Require Import List ZArith NArith String Bool.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode.
Import ListNotations.
Module JitProfile.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLPort.KLPort.
Local Open Scope string_scope.

(* Numbers cross the two semantics by these conversions. *)
Definition double_of (n : num) : N := match n with
 | NInt z => JitFloat.JitFloat.of_Z z | NFloat b => b end.

(* + - * / with a real operand. A zero divisor, integer or real, is an error (prims.c
   arithmetic), so PDiv with a zero real divisor is outside the domain. *)
Definition jit_inexact_op (p : prim) (a b : num) : option num :=
 let x := double_of a in let y := double_of b in
 match p with
 | PAdd => Some (NFloat (JitFloat.JitFloat.add x y))
 | PSub => Some (NFloat (JitFloat.JitFloat.sub x y))
 | PMul => Some (NFloat (JitFloat.JitFloat.mul x y))
 | PDiv => if JitFloat.JitFloat.is_zero y then None else Some (NFloat (JitFloat.JitFloat.div x y))
 | _ => None end.

(* Comparison with a real operand is exact: no rounding of the integer (prims.c, compare_fix_real).
   NaN compares false. *)
Definition jit_order (p : prim) (c : option comparison) : bool := match p, c with
 | PGt, Some Gt | PLt, Some Lt | PEqual, Some Eq => true
 | PGe, Some (Gt | Eq) | PLe, Some (Lt | Eq) => true
 | _, _ => false end.
Definition flip (c : option comparison) : option comparison := match c with
 | Some Lt => Some Gt | Some Gt => Some Lt | c => c end.
Definition jit_inexact_cmp (p : prim) (a b : num) : bool :=
 match a, b with
 | NInt x, NFloat y => jit_order p (JitBytecode.JitBytecode.compare_fix_real x y)
 | NFloat x, NInt y => jit_order p (flip (JitBytecode.JitBytecode.compare_fix_real y x))
 | _, _ => jit_order p (JitFloat.JitFloat.compare (double_of a) (double_of b)) end.

Definition jit_int_div (x y : Z) : num :=
 NFloat (JitFloat.JitFloat.div (JitFloat.JitFloat.of_Z x) (JitFloat.JitFloat.of_Z y)).

Definition jit_str_other (v : value) : option Observation.Observation.text := match v with
 | VStr s => Some ([34%N] ++ s ++ [34%N])%list
 | VNil => Some (of_string "()")
 | VCons _ _ => Some (of_string "#<pair>")
 | VVec _ => Some (of_string "#<absvector>")
 | VStream _ => Some (of_string "#<stream>")
 | VExn _ => Some (of_string "#<exception>")
 | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => Some (of_string "#<procedure>")
 | _ => None end.

(* Messages are not a compatibility requirement (docs/semantics.md section 8), and most
   name the offending value, which exn does not carry: Ledger OB-JIT-ERROR-TEXT. *)
Definition jit_sys_message (x : exn) : Observation.Observation.text := match x with
 | XDivZero => of_string "division by zero"
 | XCondFail => of_string "cond: no clause applies"
 | _ => of_string "error" end.

(* The clock answers in binary64. RTime carries an integer, so here that integer is the bit pattern. *)
Definition jit_time (_ : Observation.Observation.text) (z : Z) : option num :=
 if (Z.leb 0 z && Z.ltb z 18446744073709551616)%bool then Some (NFloat (Z.to_N z)) else None.

Definition jit_profile : profile := Profile
 jit_inexact_op jit_inexact_cmp jit_int_div
 JitFloat.JitFloat.format_real
 jit_str_other jit_sys_message
 (VSym (of_string "shen.fail!"))
 jit_time
 None None.

Theorem jit_division_by_zero_real : forall a b,
 JitFloat.JitFloat.is_zero (double_of b) = true -> jit_inexact_op PDiv a b = None.
Proof.
 intros a b H. unfold jit_inexact_op. cbv zeta. rewrite H. reflexivity.
Qed.

Theorem jit_absvector_fill : absvector_fill jit_profile = VSym (of_string "shen.fail!").
Proof. reflexivity. Qed.

(* --- The options --- *)
Definition byte_ok (z : Z) : bool := (Z.leb 0 z && Z.leb z 255)%bool.

(* Names defun refuses: every primitive of the table, the special forms, do and thaw (semantics.md s10). Which kernel names are sealed comes from
   the image, so it is a parameter here; relating it to the image is OB-JIT-IMAGE. *)
Definition is_fixed_name (f : name) : bool :=
 existsb (fun e => match e with (nm, _, _) => text_eqb f (of_string nm) end) JitBytecode.JitBytecode.prim_table
 || keyword f || text_eqb f (of_string "do") || text_eqb f (of_string "thaw").

Definition jit_rules (sealed : list name) : port_rules := PortRules
 (Some (JitBytecode.JitBytecode.fix_min, JitBytecode.JitBytecode.fix_max))
 byte_ok
 true
 true
 (fun _ f => negb (is_fixed_name f || existsb (text_eqb f) sealed))
 (fun k => orb (text_eqb k (of_string "run")) (text_eqb k (of_string "unix")))
 true
 (fun r => match r with
  | Observation.Observation.RHeap => Some (XUser (of_string "out of memory"))
  | Observation.Observation.RStack => Some (XUser (of_string "stack overflow")) end).

Definition fix_max_val : Z := JitBytecode.JitBytecode.fix_max.

(* A result past the fixnum range raises. *)
Theorem jit_overflow_raises : forall sealed s,
 rule_arith_r (jit_rules sealed) jit_profile PAdd Z.add [VNum (NInt fix_max_val); VNum (NInt 1)] s = dom PAdd.
Proof. intros. apply range_raises. vm_compute. reflexivity. Qed.

(* Comparison does not round: 2^53 + 1 is above the real 2^53, which a double conversion would not see. *)
Theorem jit_compare_exact :
 jit_inexact_cmp PGt (NInt 9007199254740993) (NFloat (JitFloat.JitFloat.of_Z 9007199254740992)) = true /\
 jit_inexact_cmp PEqual (NInt 9007199254740993) (NFloat (JitFloat.JitFloat.of_Z 9007199254740992)) = false.
Proof. split; vm_compute; reflexivity. Qed.

(* n->string takes a byte, not a code point. *)
Theorem jit_byte_strings : forall sealed s,
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 256)] s = dom PNToString /\
 rule_n_to_string_r (jit_rules sealed) [VNum (NInt 255)] s = ret (VStr [255%N]) s.
Proof. intros. split; reflexivity. Qed.

(* A named call of the wrong count raises, and a resource failure can be caught. *)
Theorem jit_no_partial : forall sealed g args k s ps b,
 lookup g (gfuns s) = Some (FUser ps b) -> List.length args <> List.length ps ->
 call_named_r (jit_rules sealed) jit_profile g args k s = MTau (Cfg (Throw XArity) k s).
Proof. intros. eapply no_partial_application; [reflexivity|eassumption|assumption]. Qed.

Theorem jit_resources_catchable : forall sealed k s,
 next_r (jit_rules sealed) jit_profile (Cfg (Fail Observation.Observation.RStack) k s)
 = MTau (Cfg (Throw (XUser (of_string "stack overflow"))) k s).
Proof. intros. apply catchable_resource. reflexivity. Qed.

(* defun of a primitive's name or a sealed name is refused. *)
Theorem jit_defun_fixed_refused : forall sealed rho ps b k s,
 eval_move_r (jit_rules sealed) jit_profile rho (EDefun (of_string "hd") ps b) k s
 = MTau (Cfg (Throw XBadDefinition) k s).
Proof. intros. apply defun_refused. reflexivity. Qed.

Theorem jit_defun_sealed_refused : forall sealed f rho ps b k s,
 existsb (text_eqb f) sealed = true ->
 eval_move_r (jit_rules sealed) jit_profile rho (EDefun f ps b) k s
 = MTau (Cfg (Throw XBadDefinition) k s).
Proof.
 intros sealed f rho ps b k s H. apply defun_refused. cbn [defun_allowed jit_rules]. rewrite H.
 rewrite orb_true_r. reflexivity.
Qed.

(* --- The deviation table --- *)
Inductive disposition :=
 | In_profile              (* a profile slot expresses it *)
 | In_port_rules           (* KLPort.port_rules states it, in jit_rules *)
 | In_bytecode             (* JitBytecode.v states it; the KLambda profile does not need it *)
 | Partly_stated           (* stated in part: the entry's ledger item has the rest *)
 | Ledger_only.            (* tracked; no rule states it *)

Record deviation := Dev { d_id : string; d_rule : string; d_where : disposition; d_ledger : string }.

Definition deviations : list deviation :=
 [Dev "fixnum-overflow" "integers are 62-bit; a result out of range raises integer overflow (semantics.md s3)"
    In_port_rules "OB-JIT-DEV-FIXNUM";
  Dev "ieee-doubles" "reals are binary64; mixed arithmetic gives a real" In_profile "OB-JIT-FLOAT-MODEL";
  Dev "division" "integer division exact or real; any zero divisor raises" In_profile "OB-JIT-DEV-DIVISION";
  Dev "mixed-equality" "= and comparisons across integers and reals are exact (s3); #2 fixed at this pin" In_profile "OB-JIT-ISSUE-2";
  Dev "nan-identity" "a NaN is = to itself as one object and to nothing else" In_bytecode "OB-JIT-NAN-IDENTITY";
  Dev "literals" "reader overrides make out-of-range literals reals (s3)" Ledger_only "OB-JIT-DEV-LITERALS";
  Dev "printing" "reals print shortest round-trip digits (s3)" In_profile "OB-JIT-DEV-PRINTING";
  Dev "byte-strings" "strings are bytes; n->string takes 0 to 255 (s4)" In_port_rules "OB-JIT-DEV-BYTES";
  Dev "hash" "hash is consistent with = and hashes 8 and 8.0 alike (s6)" In_bytecode "OB-JIT-DEV-HASH";
  Dev "closure-equality" "closures and streams compare by identity; two exceptions stay undefined here (s6)" Partly_stated "OB-JIT-DEV-IDENTITY";
  Dev "error-to-string" "error-to-string of a non-exception raises (s8)" In_bytecode "OB-JIT-DEV-ETS";
  Dev "cond-no-clause" "cond with no true clause raises (s9)" In_profile "OB-JIT-DEV-COND";
  Dev "no-partial" "a named call of the wrong arity raises; there is no partial application (s9)"
    In_port_rules "OB-JIT-DEV-ARITY";
  Dev "symbols-not-procedures" "applying a symbol raises (s9)" In_bytecode "OB-JIT-DEV-APPLY";
  Dev "defun-validation" "malformed defun raises at definition (s10)" Ledger_only "OB-JIT-DEV-DEFUN";
  Dev "fixed-names" "defun of a fixed name raises (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  Dev "sealing" "defun of a sealed name raises; sealed calls bind once (s10)" In_port_rules "OB-JIT-DEV-SEALING";
  Dev "lazy-lambda-form" "lambda forms are made on first fn; a placeholder before that (s11)" Ledger_only "OB-JIT-DEV-LAZY-FORM";
  Dev "get-time" "get-time takes run and unix only, and returns reals (s12)" In_port_rules "OB-JIT-DEV-TIME";
  Dev "write-failure" "a failed write-byte is not an error: fputc's result is unchecked (prims.c)"
    In_port_rules "OB-JIT-DEV-WRITE";
  Dev "char-streams" "char-stream? is false; read-unit-string and write-string raise (s12)" In_bytecode "OB-JIT-DEV-CHAR";
  Dev "catchable-resources" "stack overflow and out of memory are catchable errors (s14)"
    In_port_rules "OB-JIT-DEV-RESOURCES";
  Dev "cyclic-equality" "= on a cycle, or past its budgets, ends the process; #3's deep-term crash is fixed (s6)" Ledger_only "OB-JIT-ISSUE-3";
  Dev "factorise-cond" "define fails on a cond with no true clause (tizoc/shen-jit#1)" Ledger_only "OB-JIT-ISSUE-1"].

End JitProfile.
