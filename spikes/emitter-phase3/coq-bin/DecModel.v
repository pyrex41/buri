(** * The transcribed decoder against the model's decoder, on the compressed half.

    For every 16-bit parcel the C accepts (kind not [I_BAD]), the model's [decode_any] of any
    32-bit word with that low half gives an instruction of the same kind, length 2, with the same
    register numbers and immediate as [CfDefs.run] reads them ([bv_unsigned] of registers,
    [bv_signed] of immediates, [Z.shiftl (bv_signed imm) 12] for [lui]).  Checked on all 65,536
    parcels.  The 32-bit half is not covered here. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import BinBits DecSpec DecPost.
Import ListNotations.
Open Scope Z_scope.

Definition rg (r : reg) : Z := bv_unsigned r.

(** The C's [Ins] and a model instruction agree, field by field, on what [run] uses. *)
Definition dmatch (i : ins) (x : instr) (sz : Z) : bool :=
  (ilen i =? sz) &&
  match x with
  | OpImm ALU_ADD rd rs imm => (ik i =? I_ADDI) && (rg rd =? ird i) && (rg rs =? ir1 i) && (bv_signed imm =? iimm i)
  | OpImm ALU_AND rd rs imm => (ik i =? I_ANDI) && (rg rd =? ird i) && (rg rs =? ir1 i) && (bv_signed imm =? iimm i)
  | Op ALU_ADD rd rs1 rs2 => (ik i =? I_ADD) && (rg rd =? ird i) && (rg rs1 =? ir1 i) && (rg rs2 =? ir2 i)
  | Op ALU_XOR rd rs1 rs2 => (ik i =? I_XOR) && (rg rd =? ird i) && (rg rs1 =? ir1 i) && (rg rs2 =? ir2 i)
  | ShiftImm ALU_SLL rd rs sh => (ik i =? I_SLLI) && (rg rd =? ird i) && (rg rs =? ir1 i) && (bv_unsigned sh =? iimm i)
  | Lui rd imm => (ik i =? I_LUI) && (rg rd =? ird i) && (Z.shiftl (bv_signed imm) 12 =? iimm i)
  | Auipc rd imm => (ik i =? I_AUIPC) && (rg rd =? ird i) && (Z.shiftl (bv_signed imm) 12 =? iimm i)
  | Load SZ8 true rd rs imm => (ik i =? I_LD) && (rg rd =? ird i) && (rg rs =? ir1 i) && (bv_signed imm =? iimm i)
  | Store SZ8 rs1 rs2 imm => (ik i =? I_SD) && (rg rs1 =? ir1 i) && (rg rs2 =? ir2 i) && (bv_signed imm =? iimm i)
  | Branch c rs1 rs2 imm =>
      match c with
      | BC_EQ => ik i =? I_BEQ | BC_NE => ik i =? I_BNE | BC_LTU => ik i =? I_BLTU | BC_GEU => ik i =? I_BGEU
      | _ => false
      end && (rg rs1 =? ir1 i) && (rg rs2 =? ir2 i) && (bv_signed imm =? iimm i)
  | Jal rd imm => (ik i =? I_JAL) && (rg rd =? ird i) && (bv_signed imm =? iimm i)
  | Jalr rd rs imm => (ik i =? I_JALR) && (rg rd =? ird i) && (rg rs =? ir1 i) && (bv_signed imm =? iimm i)
  | _ => false
  end.

Definition agree16 (lo : Z) : bool :=
  (Z.land lo 3 =? 3) || (ik (dec16 lo) =? I_BAD) ||
  match decode_any (Z_to_bv 32 lo) with Some (x, sz) => (sz =? 2) && dmatch (dec16 lo) x sz | None => false end.

Lemma agree16_all : zall 65536 0 agree16 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma low16 : forall lo b2 b3, 0 <= lo < 2 ^ 16 -> 0 <= b2 < 2 ^ 8 -> 0 <= b3 < 2 ^ 8 ->
  bits 0 16 (Z_to_bv 32 (Z.lor lo (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24)))) = bits 0 16 (Z_to_bv 32 lo).
Proof.
  intros lo b2 b3 H0 H2 H3. apply bv_eq. unfold bits. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned.
  assert (Hr : forall k, 0 <= nth k [16;8;8] 0 /\ 0 <= nth k [lo;b2;b3] 0 < 2 ^ nth k [16;8;8] 0).
  { intros [|[|[|k]]]; cbn; try lia; destruct k; cbn; lia. }
  zbits_with 16%nat constr:([lo;b2;b3]) constr:([16;8;8]) Hr.
Qed.

Lemma low2 : forall lo b2 b3, 0 <= lo < 2 ^ 16 -> 0 <= b2 < 2 ^ 8 -> 0 <= b3 < 2 ^ 8 ->
  bits 0 2 (Z_to_bv 32 (Z.lor lo (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24)))) = bits 0 2 (Z_to_bv 32 lo).
Proof.
  intros lo b2 b3 H0 H2 H3. apply bv_eq. unfold bits. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned.
  assert (Hr : forall k, 0 <= nth k [16;8;8] 0 /\ 0 <= nth k [lo;b2;b3] 0 < 2 ^ nth k [16;8;8] 0).
  { intros [|[|[|k]]]; cbn; try lia; destruct k; cbn; lia. }
  zbits_with 2%nat constr:([lo;b2;b3]) constr:([16;8;8]) Hr.
Qed.

(** The bridge: whatever the two bytes above, the model decodes an accepted parcel as the C does. *)
Theorem dec16_model : forall b0 b1 b2 b3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.land b0 3 <> 3 -> ik (cdec b0 b1 b2 b3) <> I_BAD ->
  exists x, decode_any (Z_to_bv 32 (Z.lor (Z.lor b0 (Z.shiftl b1 8)) (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24))))
            = Some (x, 2) /\ dmatch (cdec b0 b1 b2 b3) x 2 = true.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3 Hlo Hk.
  set (lo := Z.lor b0 (Z.shiftl b1 8)).
  assert (Hl : 0 <= lo < 2 ^ 16).
  { split; [apply Z.lor_nonneg; split; [lia|apply Z.shiftl_nonneg; lia]|].
    apply bound_bits; [apply Z.lor_nonneg; split; [lia|apply Z.shiftl_nonneg; lia]|lia|].
    intros j Hj. unfold lo. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (tb_small b0 8 j), (tb_small b1 8 (j - 8)) by lia. reflexivity. }
  assert (L3 : Z.land lo 3 = Z.land b0 3).
  { apply Z.bits_inj'. intros i Hi. unfold lo. rewrite !Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.ltb_spec i 2) as [Hi2|Hi2].
    - rewrite (Z.testbit_neg_r b1) by lia. rewrite orb_false_r. reflexivity.
    - rewrite (tb_small 3 2 i) by lia. rewrite !andb_false_r. reflexivity. }
  assert (Ec : cdec b0 b1 b2 b3 = dec16 lo).
  { unfold cdec. fold lo. rewrite L3. destruct (Z.eqb_spec (Z.land b0 3) 3); [contradiction|reflexivity]. }
  rewrite Ec in Hk |- *.
  pose proof (zall_ok _ _ _ agree16_all lo ltac:(cbn; lia)) as A. unfold agree16 in A.
  rewrite L3, (proj2 (Z.eqb_neq _ _) Hlo), (proj2 (Z.eqb_neq _ _) Hk) in A. cbn [orb] in A.
  assert (Ed : decode_any (Z_to_bv 32 (Z.lor lo (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24)))) = decode_any (Z_to_bv 32 lo)).
  { unfold decode_any. rewrite (low2 lo b2 b3), (low16 lo b2 b3) by lia.
    destruct (decide _) as [e|e]; [exfalso|reflexivity].
    unfold bits in e. rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r in e.
    rewrite (bv_wrap_small 32 lo) in e by (change (bv_modulus 32) with (2^32); lia).
    unfold bv_wrap in e. change (bv_modulus 2) with (2^2) in e. rewrite <- Z.land_ones in e by lia.
    apply Hlo. rewrite <- L3. exact e. }
  rewrite Ed. revert A. destruct (decode_any (Z_to_bv 32 lo)) as [[x sz]|]; intro A; [|discriminate].
  apply andb_prop in A as [Asz A]. apply Z.eqb_eq in Asz. subst sz. eauto.
Qed.
