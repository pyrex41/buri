(** * The template's encodings against the model's own decoder.

    Checks, by enumerating the whole domain, that each halfword or word in [MoveTemplate]
    decodes to the instruction its form is meant to be.  This is what ties the template to
    instruction meaning, rather than to the checker's own formulas.  A compressed form is
    checked with the following halfword all zeros and all ones. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import base decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Common Require Import PropExec StepTac.
From LinuxProcessSemantics.Examples.emitter_ns Require Import MoveTemplate.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Import ListNotations.
Open Scope Z_scope.

Definition all (n : nat) (P : Z -> bool) : bool := forallb (fun i => P (Z.of_nat i)) (seq 0 n).

Lemma all_spec : forall n P, all n P = true -> forall z, 0 <= z < Z.of_nat n -> P z = true.
Proof.
  intros n P H z Hz. unfold all in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat z) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Definition is16 (x : Z) (i : instr) : bool :=
  bool_decide (decode_any (Z_to_bv 32 x) = Some (i, 2)) &&
  bool_decide (decode_any (Z_to_bv 32 (x + 65535 * 65536)) = Some (i, 2)).
Definition is32 (x : Z) (i : instr) : bool := bool_decide (decode_any (Z_to_bv 32 x) = Some (i, 4)).

Definition R (n : Z) : reg := Z_to_bv 5 n.

(** c.mv a0, r and c.mv s2, a0, for r = s2 and the home registers. *)
Lemma dec_mv_a0 : forall s, 0 <= s < 8 ->
  is16 (c_mv 10 (18 + s)) (Op ALU_ADD (R 10) (R 0) (R (18 + s))) = true.
Proof.
  intro s. exact (all_spec 8 (fun s => is16 (c_mv 10 (18 + s)) (Op ALU_ADD (R 10) (R 0) (R (18 + s))))
    ltac:(vm_cast_no_check (@eq_refl bool true)) s).
Qed.
Lemma dec_mv_keep : is16 (c_mv 18 10) (Op ALU_ADD (R 18) (R 0) (R 10)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dec_mv_cached : is16 (c_mv 10 18) (Op ALU_ADD (R 10) (R 0) (R 18)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dec_mv_home : forall d, 2 <= d < 8 -> forall s, 2 <= s < 8 -> d <> s ->
  is16 (c_mv (18 + d) (18 + s)) (Op ALU_ADD (R (18 + d)) (R 0) (R (18 + s))) = true.
Proof.
  intros d Hd s Hs _.
  exact (all_spec 8 (fun d => is16 (c_mv (18 + d) (18 + s)) (Op ALU_ADD (R (18 + d)) (R 0) (R (18 + s)))) 
    (all_spec 8 (fun s => all 8 (fun d => is16 (c_mv (18 + d) (18 + s)) (Op ALU_ADD (R (18 + d)) (R 0) (R (18 + s)))))
      ltac:(vm_cast_no_check (@eq_refl bool true)) s ltac:(lia)) d ltac:(lia)).
Qed.

(** c.ld a0, 8n(s0) and c.sd a0, 8n(s0). *)
Lemma dec_c_ld : forall n, 0 <= n < 32 ->
  is16 (c_ld_a0 (8 * n)) (Load SZ8 true (R 10) (R 8) (Z_to_bv 12 (8 * n))) = true.
Proof.
  intro n. exact (all_spec 32 (fun n => is16 (c_ld_a0 (8 * n)) (Load SZ8 true (R 10) (R 8) (Z_to_bv 12 (8 * n))))
    ltac:(vm_cast_no_check (@eq_refl bool true)) n).
Qed.
Lemma dec_c_sd : forall n, 0 <= n < 32 ->
  is16 (c_sd_a0 (8 * n)) (Store SZ8 (R 8) (R 10) (Z_to_bv 12 (8 * n))) = true.
Proof.
  intro n. exact (all_spec 32 (fun n => is16 (c_sd_a0 (8 * n)) (Store SZ8 (R 8) (R 10) (Z_to_bv 12 (8 * n))))
    ltac:(vm_cast_no_check (@eq_refl bool true)) n).
Qed.

(** ld rd, 8n(s0) and sd a0, 8n(s0), up to offset 2040. *)
Lemma dec_ld : forall n, 0 <= n < 256 ->
  is32 (ld_s0 10 (8 * n)) (Load SZ8 true (R 10) (R 8) (Z_to_bv 12 (8 * n))) = true.
Proof.
  intro n. exact (all_spec 256 (fun n => is32 (ld_s0 10 (8 * n)) (Load SZ8 true (R 10) (R 8) (Z_to_bv 12 (8 * n))))
    ltac:(vm_cast_no_check (@eq_refl bool true)) n).
Qed.
Lemma dec_ld_home : forall d, 2 <= d < 8 -> forall n, 0 <= n < 256 ->
  is32 (ld_s0 (18 + d) (8 * n)) (Load SZ8 true (R (18 + d)) (R 8) (Z_to_bv 12 (8 * n))) = true.
Proof.
  intros d Hd n Hn.
  exact (all_spec 8 (fun d => is32 (ld_s0 (18 + d) (8 * n)) (Load SZ8 true (R (18 + d)) (R 8) (Z_to_bv 12 (8 * n))))
    (all_spec 256 (fun n => all 8 (fun d => is32 (ld_s0 (18 + d) (8 * n)) (Load SZ8 true (R (18 + d)) (R 8) (Z_to_bv 12 (8 * n)))))
      ltac:(vm_cast_no_check (@eq_refl bool true)) n Hn) d ltac:(lia)).
Qed.
Lemma dec_sd : forall n, 0 <= n < 256 ->
  is32 (sd_a0 (8 * n)) (Store SZ8 (R 8) (R 10) (Z_to_bv 12 (8 * n))) = true.
Proof.
  intro n. exact (all_spec 256 (fun n => is32 (sd_a0 (8 * n)) (Store SZ8 (R 8) (R 10) (Z_to_bv 12 (8 * n))))
    ltac:(vm_cast_no_check (@eq_refl bool true)) n).
Qed.
