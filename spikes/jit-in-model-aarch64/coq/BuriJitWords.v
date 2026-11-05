(* Shen/JIT Phase 0, AArch64 spike: exact decode and sequential-behavior
   equations for the words of spikes/jit-in-model-aarch64/program.S in the
   sail-arm 7d058164 Armv9.4-A Coq model.

   Not a scripts/prove module. Evidence kind of every theorem: model theorem.
   check.sh binds every w_* line below to the built binary's bytes (the
   generated words: to the movz/movk immediates that write them) and requires a
   one-bit mutant to be rejected.

   A theorem here says what the model does with a word once something supplies
   it. It does not say that the bytes written by str are the bytes fetched:
   BuriJitMem.v shows the model leaves that open. Not proved: fetch, the rest of
   __InstructionExecute, str's execute path (address translation and MemWrite),
   DC and IC's execute paths. *)
Require Import SailStdpp.Base SailStdpp.Real SailStdpp.ConcurrencyInterfaceTypes
  SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import armv9_types arm_extras armv9.
From stdpp.bitvector Require Import definitions tactics.
Require Import BuriArm.BuriArmAdds BuriArm.BuriArmDecode BuriArm.BuriArmSeq BuriArm.BuriArmFastPath.
Import Defs.
Open Scope Z.

Transparent Z_to_bv bv_0 bv_succ bv_pred bv_add bv_sub bv_opp bv_mul bv_divu bv_modu
  bv_divs bv_quots bv_mods bv_rems bv_shiftl bv_shiftr bv_ashiftr bv_or bv_and bv_xor
  bv_not bv_zero_extend bv_sign_extend bv_extract bv_concat bv_add_Z bv_sub_Z bv_mul_Z
  bool_to_bv bv_to_bits.

(* The two words program.S generates at runtime. *)
Definition w_mov : mword 32 := Ox"52800540".
Definition w_ret : mword 32 := Ox"D65F03C0".
(* Words of program.S itself. *)
Definition w_str : mword 32 := Ox"B90000A4".
Definition w_blr : mword 32 := Ox"D63F00A0".
Definition w_isb : mword 32 := Ox"D5033FDF".
Definition w_dsb : mword 32 := Ox"D5033B9F".
Definition w_ic  : mword 32 := Ox"D50B7525".
Definition w_dc  : mword 32 := Ox"D50B7B25".

Notation "'SEE_guard' K body" :=
  (read_reg SEE >>= fun see : Z =>
     if Z.ltb see K then write_reg SEE K >> body else throw (Error_Undefined tt))
  (at level 10, K at level 0, body at level 0, only parsing).

(* ---------------- decode ---------------- *)
Theorem mov_decode pc :
  __DecodeA64 pc w_mov =
  SEE_guard 698
    (undefined_MoveWideOp tt >>= fun _ : MoveWideOp =>
     execute_aarch64_instrs_integer_ins_ext_insert_movewide 0 32 (Ox"002A") MoveWideOp_Z 0).
Proof. unfold w_mov. chain. Qed.

Theorem ret_decode pc :
  __DecodeA64 pc w_ret =
  SEE_guard 94
    (undefined_BranchType tt >>= fun _ : BranchType =>
     execute_aarch64_instrs_branch_unconditional_register BranchType_RET 0 30 false false true).
Proof. unfold w_ret. chain. Qed.

Theorem str_decode pc :
  __DecodeA64 pc w_str =
  SEE_guard 648
    (undefined_MemOp tt >>= fun _ : MemOp =>
     undefined_bool tt >>= fun _ : bool =>
     undefined_Constraint tt >>= fun _ : Constraint =>
     execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
       32 MemOp_STORE 5 false (Ox"0000000000000000") false 32 false false 4 true false false).
Proof. unfold w_str. chain. Qed.

Theorem blr_decode pc :
  __DecodeA64 pc w_blr =
  SEE_guard 90
    (undefined_BranchType tt >>= fun _ : BranchType =>
     execute_aarch64_instrs_branch_unconditional_register BranchType_INDCALL 0 5 false false true).
Proof. unfold w_blr. chain. Qed.

Theorem isb_decode pc :
  __DecodeA64 pc w_isb =
  SEE_guard 483 (execute_aarch64_instrs_system_barriers_isb tt).
Proof. unfold w_isb. chain. Qed.

Theorem dsb_decode pc :
  __DecodeA64 pc w_dsb =
  SEE_guard 197
    (undefined_DSBAlias tt >>= fun _ : DSBAlias =>
     undefined_MBReqDomain tt >>= fun _ : MBReqDomain =>
     undefined_MBReqTypes tt >>= fun _ : MBReqTypes =>
     execute_aarch64_instrs_system_barriers_dsb DSBAlias_DSB MBReqDomain_InnerShareable false MBReqTypes_All).
Proof. unfold w_dsb. chain. Qed.

Theorem ic_decode pc :
  __DecodeA64 pc w_ic =
  SEE_guard 1004
    (AArch64_CheckSystemAccess ('b"01") ('b"011") (Ox"7") (Ox"5") ('b"001") ('b"00101") ('b"0") >>
     execute_aarch64_instrs_system_sysops false 5 7 3 1 5).
Proof. unfold w_ic. chain. Qed.

Theorem dc_decode pc :
  __DecodeA64 pc w_dc =
  SEE_guard 1004
    (AArch64_CheckSystemAccess ('b"01") ('b"011") (Ox"7") (Ox"B") ('b"001") ('b"00101") ('b"0") >>
     execute_aarch64_instrs_system_sysops false 11 7 3 1 5).
Proof. unfold w_dc. chain. Qed.

Print Assumptions mov_decode.
Print Assumptions ret_decode.
Print Assumptions str_decode.
Print Assumptions blr_decode.
Print Assumptions isb_decode.
Print Assumptions dsb_decode.
Print Assumptions ic_decode.
Print Assumptions dc_decode.
