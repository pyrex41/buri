From Coq Require Import List NArith String Ascii.
From Buri Require Import JitBytecode JitLowerStage0 JitImage ImgData ImgRun ImgSum.
Import ListNotations JitLowerStage0.JitLowerStage0 JitImage.JitImage.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.
(* Mutant A: print's code object arity word 1 -> 2. Mutant B: print's first bytecode byte
   0x02 (const) -> 0x00 (move). Each must turn print's verdict from Match to Differ. *)
Definition mutA := B.tset (key 10097) 2 m0.
Definition mutB := B.tset (key 31327) (N.lxor (get m0 31327) 2) m0.
Definition run (m : mem) := match parse_image m nwords with
 | Some (_, c) => Some (let '(n, bad) := tally c (map to_val sbc_writer) in (n, map vf bad)) | None => None end.
Definition r_base := Eval vm_compute in run m0. Print r_base.
Definition r_mutA := Eval vm_compute in run mutA. Print r_mutA.
Definition r_mutB := Eval vm_compute in run mutB. Print r_mutB.
