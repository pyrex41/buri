(* Probe, not a Buri proof module and not in scripts/prove: it needs the
   separate toolchain of docs/ARM-FOUNDATION.md (nixpkgs Coq 8.18.0, stdpp
   1.10.0, coq-sail-stdpp 0.19, sail-arm 7d058164 arm-v9.4-a Coq snapshot).
   Question: does the exact Chez word at kl:buri-arm-add+0x14 (bytes
   17 00 01 ab, word 0xab010017) decode in the authoritative Sail model to the
   ADDS (shifted register) execute call with d=23, n=0, m=1, 64-bit, flags on?
   OUTCOME (1 Nov 2026): the stated pure equation is the WRONG SHAPE and the
   attempt ends in Abort.  Guard-by-guard reduction exposes that the decoder
   is monadic: guards are `and_boolM` over `read_reg SEE` and taken branches
   `write_reg SEE _` before calling decode_*/execute_*.  A correct statement is
   about the monadic program (or a Hoare triple in coq-sail's Hoare.v) under a
   premise on SEE.  Nothing here is a theorem; the file is kept as a record. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
Import Defs.
Open Scope Z.

Definition chez_word_0014 : mword 32 := Ox"AB010017".

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(* Decide each closed bitvector guard by vm_compute, one at a time. *)
Ltac decide_guard :=
  match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch b with true => fail | false => fail | _ =>
        let v := eval vm_compute in b in
        let H := fresh in
        assert (H : b = v) by (vm_compute; reflexivity);
        rewrite H; clear H; cbv beta iota
      end
  end.

Ltac step :=
  match goal with
  | |- ?l = execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg _ _ _ _ _ _ _ _ =>
      let h := head_of l in
      lazymatch h with
      | execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg => fail
      | bind0 => cbn [bind0 bind returnM]
      | bind => cbn [bind returnM]
      | _ => unfold h; cbv zeta
      end
  end.

Lemma chez_0014_decodes_to_adds :
  __DecodeA64 0 chez_word_0014 =
  execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
    23 64 1 0 true 0 ShiftType_LSL false.
Proof.
  Time (repeat (first [decide_guard | step])).
  Show.
Abort.
