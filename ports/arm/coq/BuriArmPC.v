(* E2E-20 Wave D: the PC advance of the sail-arm Armv9.4-A model.

   NOT a scripts/prove module (docs/ARM-FOUNDATION.md section 12; checked by
   scripts/check-arm.sh Part B).

   The model advances the PC at the end of __InstructionExecute, after the
   instruction's decode and execute (__DecodeExecute), SPE post-execution,
   the InGuardedPage reset and the BTYPE update:

     read_reg __BranchTaken >>= fun w => (if negb w then
        _PC := (_PC + ThisInstrLength/8)[63:0] else skip) >> ...

   InstructionExecute_pc_part: __InstructionExecute is, by conversion, the
   definition InstructionExecute_with below (a verbatim copy of the model's
   text) applied to pc_part, the model's own PC-advance code.  So pc_part is
   exactly the model's PC step, at exactly that point.
   pc_part_not_taken / pc_part_taken (IFFs in the sequential reading of
   BuriArmSeq.v): if the instruction did not set __BranchTaken and the
   current encoding is A64, the step's only behaviour writes
   _PC := _PC + 4; if __BranchTaken is set, it changes nothing.
   pc_next_bv: the written value is the bit-vector sum _PC + 4, the value
   isla's isla_footprint_no_init wrapper writes (`_PC += 4`).

   __InstructionExecute writes __BranchTaken := false before __DecodeExecute,
   and the encoding comes from __FetchInstr / __SetThisInstrDetails.  Those
   steps, and everything else in __InstructionExecute (fetch, debug and PMU
   events, SPE, BTYPE, single-step), are NOT proved here.

   Trusted: Coq 8.19.0, coq-sail 0.19, the Sail-to-Coq translation of
   sail-arm 7d058164.  Nothing here mentions __DecodeA64; the audit lists
   what each theorem depends on. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmSeq.
Import Defs.
Open Scope Z.

Transparent Z_to_bv bv_0 bv_succ bv_pred bv_add bv_sub bv_opp bv_mul bv_divu bv_modu
  bv_divs bv_quots bv_mods bv_rems bv_shiftl bv_shiftr bv_ashiftr bv_or bv_and bv_xor
  bv_not bv_zero_extend bv_sign_extend bv_extract bv_concat bv_add_Z bv_sub_Z bv_mul_Z
  bool_to_bv bv_to_bits.

Definition pc_part (w__11 : bool) : M unit :=
   (if negb (w__11) return M (unit) then
      ((read_reg _PC)  : M (mword 64)) >>= fun (w__12 : mword 64) =>
      (ThisInstrLength (tt)) >>= fun (w__13 : Z) =>
      write_reg _PC (subrange_vec_dec ((add_vec_int (w__12) ((fdiv_int (w__13) (8))))) (63) (0))
       : M (unit)
    else returnM (tt)).

Definition InstructionExecute_with (pc_step : bool -> M unit) : M (unit) :=
   (undefined___InstrEnc (tt)) >>= fun (enc : __InstrEnc) =>
   (undefined_bitvector (32)) >>= fun (instr : bits 32) =>
   (EDSCR_read (tt)) >>= fun (w__0 : mword 32) =>
   (EDSCR_write ((_update_EDSCR_Type_PipeAdv (w__0) ((('b"1")  : mword 1))))) >>
   ((read_reg EDESR)  : M (mword 32)) >>= fun (w__1 : mword 32) =>
   (if negb ((IsZero (w__1))) return M (unit) then
      (CheckPendingOSUnlockCatch (tt)) >>
      (CheckPendingResetCatch (tt)) >> (CheckPendingExceptionCatch (true))  : M (unit)
    else returnM (tt)) >>
   (try_catch ((and_boolM
                  (read_reg PSTATE >>= fun (w__2 : ProcState) =>
                   returnM (((eq_vec (w__2.(ProcState_nRW)) ((('b"1")  : mword 1)))  : bool)))
                  (read_reg PSTATE >>= fun (w__3 : ProcState) =>
                   returnM (((eq_vec (w__3.(ProcState_T)) ((('b"1")  : mword 1)))  : bool)))) >>= fun (w__4 : bool) =>
               write_reg ShouldAdvanceIT w__4 >>
               write_reg ShouldAdvanceSS true >>
               (ThisInstrAddr (64)) >>= fun (pc : bits 64) =>
               (__FetchInstr (pc)) >>= fun (w__5 : (__InstrEnc * mword 32)) =>
               let '((tup__0, tup__1)) := w__5  : (__InstrEnc * mword 32) in
               let enc : __InstrEnc := tup__0 in
               let instr : bits 32 := tup__1 in
               (__CheckForEmulatorTermination (enc) (instr)) >>
               (PMUEvent (PMU_EVENT_INST_SPEC)) >>
               write_reg __BranchTaken false >>
               write_reg __ExclusiveMonitorSet false >>
               (__DefaultCond (enc)) >>= fun (w__6 : mword 4) =>
               (__SetThisInstrDetails (enc) (instr) (w__6)) >>
               (SPEPreExecution (tt)) >>
               (__DecodeExecute (enc) (instr)) >> (PMUEvent (PMU_EVENT_INST_RETIRED))  : M (unit)) (fun __catch_val => match __catch_val with 
    | exn =>
       (if orb ((orb ((IsSEE (exn))) ((IsUNDEFINED (exn))))) ((IsUNPREDICTABLE (exn)))
          return
          M (unit) then
          (UsingAArch32 (tt)) >>= fun (w__7 : bool) =>
          (if w__7 return M (unit) then
             (match enc with
              | __A32 => (UnallocatedA32_Instruction (instr))  : M (unit)
              | __T16 =>
                 (UnallocatedT32_16_Instruction ((subrange_vec_dec (instr) (15) (0))))  : M (unit)
              | __T32 => (UnallocatedT32_32_Instruction (instr))  : M (unit)
              | _ => (Unreachable (tt))  : M (unit)
              end)
              : M (unit)
           else (AArch64_UndefinedFault (tt))  : M (unit))
           : M (unit)
        else if IsExceptionTaken (exn) then returnM (tt)
        else throw exn)
        : M (unit)
    end)) >>
   (SPEPostExecution (tt)) >>
   write_reg InGuardedPage false >>
   (AArch64_ExecutingERETInstr (tt)) >>= fun (w__8 : bool) =>
   (if negb (w__8) return M (unit) then
      read_reg PSTATE >>= fun (w__9 : ProcState) =>
      ((read_reg BTypeNext)  : M (mword 2)) >>= fun (w__10 : mword 2) =>
      write_reg PSTATE {[ w__9 with ProcState_BTYPE := w__10 ]}
       : M (unit)
    else returnM (tt)) >>
   read_reg __BranchTaken >>= fun (w__11 : bool) =>
   (pc_step w__11) >>
   read_reg ShouldAdvanceIT >>= fun (w__14 : bool) =>
   (if w__14 return M (unit) then (AArch32_ITAdvance (tt))  : M (unit)
    else returnM (tt)) >>
   read_reg ShouldAdvanceSS >>= fun (w__15 : bool) =>
   (if w__15 return M (unit) then (SSAdvance (tt))  : M (unit)
    else returnM (tt))
    : M (unit).

Theorem InstructionExecute_pc_part : __InstructionExecute tt = InstructionExecute_with pc_part.
Proof. reflexivity. Qed.

Definition pc_next_val (pc : mword 64) : mword 64 := subrange_vec_dec (add_vec_int pc (fdiv_int 32 8)) 63 0.
Definition pc_next (rs : regstate) : regstate :=
  register_set _PC (pc_next_val (register_lookup _PC rs)) rs.

Theorem pc_part_not_taken rs rs' a : register_lookup __ThisInstrEnc rs = __A64 ->
  sexec rs (pc_part false) rs' a <-> rs' = pc_next rs /\ a = tt.
Proof.
  intros Henc. split.
  - intros H. sx_bwd H. destruct H as [-> ->]. split; [|reflexivity].
    unfold pc_next. destruct rs; reflexivity.
  - intros [-> ->]. eapply sexec_eq; [sx_fwd|]. unfold pc_next. destruct rs; reflexivity.
Qed.

Theorem pc_part_taken rs rs' a : sexec rs (pc_part true) rs' a <-> rs' = rs /\ a = tt.
Proof.
  split.
  - intros H. sx_bwd H. destruct H as [-> ->]. split; reflexivity.
  - intros [-> ->]. apply SRet.
Qed.

Lemma pc_next_bv (pc : mword 64) : pc_next_val pc = bv_add pc (BV 64 4).
Proof.
  apply bv_eq. unfold pc_next_val, subrange_vec_dec, to_word_idx, add_vec_int, add_vec, word_binop,
    with_word', with_word, mword_of_int, MachineWord.MachineWord.add.
  rewrite !(autocast_eq _ eq_refl), cast_Z_refl.
  cbn -[bv_add bv_extract Z_to_bv].
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice, get_word, to_word, MachineWord.MachineWord.Z_to_word.
  change (Z.to_N (63 - 0 + 1)) with 64%N.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !bv_add_unsigned, Z_to_bv_unsigned.
  change (32 `quot` 8) with 4. change (bv_unsigned (BV 64 4)) with 4.
  replace (bv_wrap 64 4) with 4 by reflexivity.
  unfold bv_wrap. rewrite Zmod_mod. reflexivity.
Qed.

(* The step as a function of the record: skip if a branch was taken. *)
Definition pc_after (rs : regstate) : regstate :=
  if register_lookup __BranchTaken rs then rs else pc_next rs.

Theorem pc_part_after rs rs' a : register_lookup __ThisInstrEnc rs = __A64 ->
  sexec rs (read_reg __BranchTaken >>= pc_part) rs' a <-> rs' = pc_after rs /\ a = tt.
Proof.
  intros Henc. unfold pc_after.
  destruct (register_lookup __BranchTaken rs) eqn:Eb; split.
  - intros H. sx_bwd H. destruct H as [-> ->]. split; reflexivity.
  - intros [-> ->]. eapply sexec_eq; [sx_fwd|]. reflexivity.
  - intros H. sx_bwd H. destruct H as [-> ->]. split; [|reflexivity].
    unfold pc_next. destruct rs; reflexivity.
  - intros [-> ->]. eapply sexec_eq; [sx_fwd|]. unfold pc_next. destruct rs; reflexivity.
Qed.

Lemma subrange_add_bv (pc off : mword 64) : subrange_vec_dec (add_vec pc off) 63 0 = bv_add pc off.
Proof.
  apply bv_eq. unfold subrange_vec_dec, to_word_idx, add_vec, word_binop,
    with_word', with_word, MachineWord.MachineWord.add.
  rewrite !(autocast_eq _ eq_refl).
  cbn -[bv_add bv_extract Z_to_bv].
  rewrite MachineWord.MachineWord.cast_idx_refl.
  rewrite cast_Z_refl. unfold MachineWord.MachineWord.slice, get_word, to_word.
  change (Z.to_N (63 - 0 + 1)) with 64%N.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !bv_add_unsigned.
  unfold bv_wrap. rewrite Zmod_mod. reflexivity.
Qed.

Lemma eq_vec_1 (z : mword 1) : eq_vec z ('b"1") = bool_decide (z = 1%bv).
Proof.
  unfold eq_vec, MachineWord.MachineWord.eqb, get_word.
  apply bool_decide_ext.
  assert (H1 : ('b"1" : mword 1) = 1%bv) by (apply bv_eq; reflexivity).
  rewrite H1. reflexivity.
Qed.

Print Assumptions InstructionExecute_pc_part.
Print Assumptions pc_part_not_taken.
Print Assumptions pc_part_taken.
Print Assumptions pc_next_bv.
Print Assumptions pc_part_after.
Print Assumptions subrange_add_bv.
Print Assumptions eq_vec_1.
