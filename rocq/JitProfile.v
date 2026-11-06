(* Shen/JIT Phase 1: the Shen/JIT semantic profile, in the slots of KLValue.profile, and
   the table of what those slots cannot express. A profile fixes parameters of Buri's
   KLambda semantics; it does not change its rules. The rules this port breaks are listed
   in `deviations`, each with the ledger entry that tracks it. The profile being
   definable does not mean the port refines the semantics under it: it does not, until the
   gaps marked Needs_semantics_change are resolved. *)
From Coq Require Import List ZArith NArith String Bool.
From Buri Require Import Observation KLSyntax KLValue JitFloat JitBytecode.
Import ListNotations.
Module JitProfile.
Import KLSyntax.KLSyntax KLValue.KLValue.
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

(* Comparison with a real operand converts a fixnum to a double. This is what the pinned
   code does; docs/semantics.md says mathematical value. Ledger: OB-JIT-ISSUE-2. *)
Definition jit_inexact_cmp (p : prim) (a b : num) : bool :=
 let x := double_of a in let y := double_of b in
 match p with
 | PGt => JitFloat.JitFloat.gt x y | PLt => JitFloat.JitFloat.lt x y
 | PGe => JitFloat.JitFloat.ge x y | PLe => JitFloat.JitFloat.le x y
 | PEqual => JitFloat.JitFloat.eqv x y
 | _ => false end.

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

Definition jit_profile : profile := Profile
 jit_inexact_op jit_inexact_cmp jit_int_div
 JitFloat.JitFloat.format_real
 jit_str_other jit_sys_message
 (VSym (of_string "shen.fail!"))
 (fun _ _ => None)  (* the clock arrives as a double, which QTime's integer cannot carry *)
 None None.

Theorem jit_division_by_zero_real : forall a b,
 JitFloat.JitFloat.is_zero (double_of b) = true -> jit_inexact_op PDiv a b = None.
Proof.
 intros a b H. unfold jit_inexact_op. cbv zeta. rewrite H. reflexivity.
Qed.

Theorem jit_absvector_fill : absvector_fill jit_profile = VSym (of_string "shen.fail!").
Proof. reflexivity. Qed.

(* --- The deviation table --- *)
Inductive disposition :=
 | In_profile              (* a profile slot expresses it *)
 | In_bytecode             (* JitBytecode.v states it; the KLambda profile does not need it *)
 | Needs_semantics_change  (* Buri's KLambda rules contradict it: proposal, not done *)
 | Ledger_only.            (* tracked; no rule states it *)

Record deviation := Dev { d_id : string; d_rule : string; d_where : disposition; d_ledger : string }.

Definition deviations : list deviation :=
 [Dev "fixnum-overflow" "integers are 62-bit; a result out of range raises integer overflow (semantics.md s3)"
    Needs_semantics_change "OB-JIT-DEV-FIXNUM";
  Dev "ieee-doubles" "reals are binary64; mixed arithmetic gives a real" In_profile "OB-JIT-FLOAT-MODEL";
  Dev "division" "integer division exact or real; any zero divisor raises" In_profile "OB-JIT-DEV-DIVISION";
  Dev "mixed-equality" "= compares numbers by converting to double (s3, tizoc/shen-jit#2)" In_profile "OB-JIT-ISSUE-2";
  Dev "nan-identity" "a NaN is = to itself as one object and to nothing else" In_bytecode "OB-JIT-NAN-IDENTITY";
  Dev "literals" "reader overrides make out-of-range literals reals (s3)" Ledger_only "OB-JIT-DEV-LITERALS";
  Dev "printing" "reals print shortest round-trip digits (s3)" In_profile "OB-JIT-DEV-PRINTING";
  Dev "byte-strings" "strings are bytes; n->string takes 0 to 255 (s4)" Needs_semantics_change "OB-JIT-DEV-BYTES";
  Dev "hash" "hash is consistent with = and hashes 8 and 8.0 alike (s6)" In_bytecode "OB-JIT-DEV-HASH";
  Dev "closure-equality" "closures, streams and exceptions compare by identity (s6)" Needs_semantics_change "OB-JIT-DEV-IDENTITY";
  Dev "error-to-string" "error-to-string of a non-exception raises (s8)" In_bytecode "OB-JIT-DEV-ETS";
  Dev "cond-no-clause" "cond with no true clause raises (s9)" In_profile "OB-JIT-DEV-COND";
  Dev "no-partial" "a named call of the wrong arity raises; there is no partial application (s9)"
    Needs_semantics_change "OB-JIT-DEV-ARITY";
  Dev "symbols-not-procedures" "applying a symbol raises (s9)" In_bytecode "OB-JIT-DEV-APPLY";
  Dev "defun-validation" "malformed defun raises at definition (s10)" Ledger_only "OB-JIT-DEV-DEFUN";
  Dev "fixed-names" "defun of a fixed name raises (s10)" Needs_semantics_change "OB-JIT-DEV-SEALING";
  Dev "sealing" "defun of a sealed name raises; sealed calls bind once (s10)" Needs_semantics_change "OB-JIT-DEV-SEALING";
  Dev "lazy-lambda-form" "lambda forms are made on first fn; a placeholder before that (s11)" Ledger_only "OB-JIT-DEV-LAZY-FORM";
  Dev "get-time" "get-time takes run and unix only, and returns reals (s12)" Needs_semantics_change "OB-JIT-DEV-TIME";
  Dev "write-failure" "a failed write-byte is not an error: fputc's result is unchecked (prims.c)"
    Needs_semantics_change "OB-JIT-DEV-WRITE";
  Dev "char-streams" "char-stream? is false; read-unit-string and write-string raise (s12)" In_bytecode "OB-JIT-DEV-CHAR";
  Dev "catchable-resources" "stack overflow and out of memory are catchable errors (s14)"
    Needs_semantics_change "OB-JIT-DEV-RESOURCES";
  Dev "deep-equality" "= on a deep term crashes past trap-error (tizoc/shen-jit#3)" Ledger_only "OB-JIT-ISSUE-3";
  Dev "factorise-cond" "define fails on a cond with no true clause (tizoc/shen-jit#1)" Ledger_only "OB-JIT-ISSUE-1"].

Definition change_needed (d : deviation) : bool := match d_where d with
 | Needs_semantics_change => true | _ => false end.
End JitProfile.
