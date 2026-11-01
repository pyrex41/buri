(* Islaris proof of the fixnum fast path of kl:buri-arm-add as compiled by
   Chez Scheme 10.3.0 tarm64le (ports/arm/chez, bytes 0x00-0x23), placed at
   the captured instance's address 0x7f8d409bcb50.

   Separate toolchain: Coq 8.19.0 + Iris/Lithium/Islaris pinned in
   nix/arm/islaris.nix; checked by ports/arm/islaris/check-islaris.sh.  NOT
   a scripts/prove module.

   Evidence kind: an Iris/Islaris separation-logic theorem, universally
   quantified over the operands, about the isla traces in
   isla.instructions.buri_chez_add.  Islaris's adequacy theorem relates
   those traces to Islaris's own operational semantics of traces.  The traces
   themselves are isla output (isla + z3 over the Sail Armv8.5 model
   isla-snapshots armv8p5.ir, under Islaris's EL2 / MMU-off register
   constraints etc/aarch64_isla_coq.toml), so the link "trace = architecture"
   is trusted, not proved.  In particular this is NOT a theorem about the
   sail-arm Armv9.4 Coq model of ports/arm/coq/BuriArmAdds.v.

   Statement: started at +0x00 with X23 = 2 (Chez's argument count), X0 = a,
   X1 = b, (a|b) & 7 = 0 (both fixnum-tagged), a + b without signed
   overflow, and X20 pointing at an 8-byte-aligned, below-2^52 frame slot
   holding the return address ra, the code reaches ra with X23 = a + b,
   X30 = a | b and X10 = ra; X0, X1, X20 and the frame slot are unchanged.
   The two slow-path branches (+0x84 argument error, +0x24 generic `+`) are
   shown infeasible under these premises: they are mapped to `instr _ None`,
   so reaching them would be a stuck/trap state the proof would have to
   justify. *)
Require Import isla.aarch64.aarch64.
From isla.instructions.buri_chez_add Require Import instrs.

(* A taken slow-path branch carries a pure hypothesis contradicting the
   premises (the trace's own Assert); close it.  coqc checks the proof. *)
Ltac slow_path_infeasible :=
  exfalso;
  first [ discriminate
        | match goal with H : _ ≠ _ |- _ => apply H end;
          repeat match goal with x := _ |- _ => progress unfold x end;
          first [ assumption | bv_solve ] ].

Definition buri_add_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (a b fp ra r10 r30 : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R23" ↦ᵣ RVal_Bits (BV 64 2) ∗
  "R0" ↦ᵣ RVal_Bits a ∗ "R1" ↦ᵣ RVal_Bits b ∗
  "R30" ↦ᵣ RVal_Bits r30 ∗ "R10" ↦ᵣ RVal_Bits r10 ∗
  "R20" ↦ᵣ RVal_Bits fp ∗
  "InGuardedPage" ↦ᵣ RVal_Bool false ∗
  bv_unsigned fp ↦ₘ ra ∗
  ⌜bv_unsigned fp < 2 ^ 52⌝ ∗ ⌜bv_unsigned fp `mod` 8 = 0⌝ ∗
  ⌜bv_and (bv_or a b) (BV 64 7) = BV 64 0⌝ ∗
  ⌜- 2 ^ 63 ≤ bv_signed a + bv_signed b < 2 ^ 63⌝ ∗
  instr_pre (bv_unsigned ra) (
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R23" ↦ᵣ RVal_Bits (bv_add a b) ∗
    "R0" ↦ᵣ RVal_Bits a ∗ "R1" ↦ᵣ RVal_Bits b ∗
    "R30" ↦ᵣ RVal_Bits (bv_or a b) ∗ "R10" ↦ᵣ RVal_Bits ra ∗
    "R20" ↦ᵣ RVal_Bits fp ∗
    "InGuardedPage" ↦ᵣ RVal_Bool false ∗
    bv_unsigned fp ↦ₘ ra ∗
    True).
Arguments buri_add_spec /.

Lemma buri_chez_add_fast_path `{!islaG Σ} `{!threadG} :
  instr 0x00007f8d409bcb50 (Some a0) -∗
  instr 0x00007f8d409bcb54 (Some a4) -∗
  instr 0x00007f8d409bcb58 (Some a8) -∗
  instr 0x00007f8d409bcb5c (Some ac) -∗
  instr 0x00007f8d409bcb60 (Some a10) -∗
  instr 0x00007f8d409bcb64 (Some a14) -∗
  instr 0x00007f8d409bcb68 (Some a18) -∗
  instr 0x00007f8d409bcb6c (Some a1c) -∗
  instr 0x00007f8d409bcb70 (Some a20) -∗
  instr 0x00007f8d409bcb74 None -∗
  instr 0x00007f8d409bcbd4 None -∗
  instr_body 0x00007f8d409bcb50 buri_add_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve.
  (* Besides side conditions, what remains are the taken slow-path branches,
     stuck at an `instr _ None` address. *)
  all: try slow_path_infeasible.
  all: prepare_sidecond.
  all: try bv_solve.
  Unshelve.
  all: try slow_path_infeasible.
Qed.
