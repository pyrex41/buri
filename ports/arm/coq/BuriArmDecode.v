(* E2E-20 Wave C: exact decode equations for captured words in the sail-arm
   Armv9.4-A Coq model (sail-arm 7d058164).

   NOT a scripts/prove module.  Separate toolchain: Coq 8.19.0 + the Islaris
   stdpp/iris pins (nix/arm/islaris.nix) + coq-sail 0.19 src-stdpp + the
   arm-v9.4-a Coq snapshot, all built by nix/arm/sail-model.nix or the
   recipe in ports/arm/coq/README-toolchain.md.  Checked only by the opt-in
   scripts/check-arm.sh, which first binds every `Definition *_word_* :=
   Ox"..."` line below to the stored captured bytes.

   Evidence kind of every theorem here: model theorem, universal over the
   decoder's `pc` argument.  Each is an equation between iMon trees, so it
   fixes every behaviour of the model's decoder on that word: which encoding
   it selects, the SEE retry guard, every register read the decoder does,
   and the exact arguments of the execute function it calls.  It does NOT
   describe what the execute function does (memory access, branch, trap).

   Words (offsets are into the stored code bytes):
     Chez 10.3.0 tarm64le kl:buri-arm-add (ports/arm/chez/chez1030-buri-arm-add.bin)
       +0x00 cmp x23,#2  +0x04 b.ne  +0x08 orr x30,x0,x1  +0x0c tst x30,#7
       +0x10 b.ne  +0x18 b.vs  +0x1c ldur x10,[x20]  +0x20 br x10
       +0x2c str x0,[x20,#8]                                  (store)
     SBCL 2.6.8 aarch64 Shen-CL buri-arm-add (ports/arm/sbcl/sbcl-buri-arm-add.bin)
       +0x210 ret                                             (return)
       +0x2a0 blr x10, the call into ALLOC-TRAMP              (call)
       +0x264 brk #15, the invalid-argument-count trap        (fault path)
   (+0x14 adds is in BuriArmAdds.v.)  Mnemonics are reading aids only.

   Method: `chain` eliminates the decoder's closed guards from the head of
   the term, one at a time, deciding each closed Boolean with vm_compute
   and stepping with substitution lemmas (guard_skip / guard_take); the
   selected decode function is then compared with the stated body by
   conversion.  Every guard of every group is decided; none is assumed.
   Trusted: the Sail-to-Coq translation, coq-sail 0.19, Coq 8.19.0 with
   stdpp (Islaris pin), the vm_compute kernel path, and the three Coq
   standard-library axioms that `Print Assumptions __DecodeA64` lists. *)
Require Import SailStdpp.Base SailStdpp.Real SailStdpp.ConcurrencyInterfaceTypes
  SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import armv9_types arm_extras armv9.
Import Defs.
Open Scope Z.

(* ---------------------------------------------------------------- *)
(* Guard elimination.  Each lemma is a substitution, so proof terms share
   the untouched remainder of the decoder. *)
Lemma guard_skip {A} b (X : M bool) (T E R : M A) :
  b = false -> E = R ->
  (and_boolM (returnM b) X >>= fun w => if w then T else E) = R.
Proof. intros -> ->. reflexivity. Qed.

Lemma guard_take {A} b K (T E E' R : M A) :
  b = true -> E = E' ->
  (read_reg SEE >>= fun see : Z => if Z.ltb see K then T else E') = R ->
  (and_boolM (returnM b) (read_reg SEE >>= fun w : Z => returnM (Z.ltb w K))
     >>= fun w => if w then T else E) = R.
Proof. intros -> -> <-. reflexivity. Qed.

Lemma if_skip {A} b (T E R : M A) : b = false -> E = R -> (if b then T else E) = R.
Proof. intros -> ->. reflexivity. Qed.
Lemma if_take {A} b (T E R : M A) : b = true -> T = R -> (if b then T else E) = R.
Proof. intros -> ->. reflexivity. Qed.

Ltac vmdec := vm_compute; reflexivity.

Ltac chain :=
  lazymatch goal with
  | |- (and_boolM (returnM ?b) ?X >>= fun w => if w then ?T else ?E) = _ =>
      let v := eval vm_compute in b in
      lazymatch v with
      | false => refine (guard_skip b X T E _ ltac:(vmdec) _); chain
      | true => refine (guard_take b _ T E _ _ ltac:(vmdec) _ _); [chain | reflexivity]
      end
  | |- (if ?b then ?T else ?E) = _ =>
      let v := eval vm_compute in b in
      lazymatch v with
      | false => refine (if_skip b T E _ ltac:(vmdec) _); chain
      | true => refine (if_take b T E _ ltac:(vmdec) _); chain
      end
  | |- __DecodeA64 _ _ = _ => unfold __DecodeA64; chain
  | |- __DecodeA64_LoadStore _ _ = _ => unfold __DecodeA64_LoadStore; chain
  | |- __DecodeA64_BranchExcSys _ _ = _ => unfold __DecodeA64_BranchExcSys; chain
  | |- __DecodeA64_DataProcImm _ _ = _ => unfold __DecodeA64_DataProcImm; chain
  | |- __DecodeA64_DataProcReg _ _ = _ => unfold __DecodeA64_DataProcReg; chain
  | |- _ = _ => reflexivity
  end.

(* ---------------------------------------------------------------- *)
(* The captured words; scripts/check-arm.sh regenerates each line from the
   stored bytes and compares. *)
Definition chez_word_0000 : mword 32 := Ox"F1000AFF".
Definition chez_word_0004 : mword 32 := Ox"54000401".
Definition chez_word_0008 : mword 32 := Ox"AA01001E".
Definition chez_word_000c : mword 32 := Ox"F2400BDF".
Definition chez_word_0010 : mword 32 := Ox"540000A1".
Definition chez_word_0018 : mword 32 := Ox"54000066".
Definition chez_word_001c : mword 32 := Ox"F840028A".
Definition chez_word_0020 : mword 32 := Ox"D61F0140".
Definition chez_word_002c : mword 32 := Ox"F9000680".
Definition sbcl_word_0210 : mword 32 := Ox"D65F03C0".
Definition sbcl_word_0264 : mword 32 := Ox"D42001E0".
Definition sbcl_word_02a0 : mword 32 := Ox"D63F0140".

Notation "'SEE_guard' K body" :=
  (read_reg SEE >>= fun see : Z =>
     if Z.ltb see K then write_reg SEE K >> body else throw (Error_Undefined tt))
  (at level 10, K at level 0, body at level 0, only parsing).

(* +0x00 cmp x23, #2  =  SUBS XZR, X23, #2 (encoding 21 of DataProcImm) *)
Theorem chez_0000_decode pc :
  __DecodeA64 pc chez_word_0000 =
  SEE_guard 21
    (undefined_bitvector (__id 64) >>= fun _ : bits 64 =>
     execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
       31 64 (Ox"0000000000000002") 23 true true).
Proof. unfold chez_word_0000. chain. Qed.

(* +0x04 b.ne +0x84 : cond 0b0001, offset 0x80 *)
Theorem chez_0004_decode pc :
  __DecodeA64 pc chez_word_0004 =
  SEE_guard 69
    (execute_aarch64_instrs_branch_conditional_cond ('b"0001") (Ox"0000000000000080")).
Proof. unfold chez_word_0004. chain. Qed.

(* +0x08 orr x30, x0, x1 (ORR shifted register, LSL #0) *)
Theorem chez_0008_decode pc :
  __DecodeA64 pc chez_word_0008 =
  SEE_guard 55
    (undefined_bool tt >>= fun _ : bool =>
     undefined_LogicalOp tt >>= fun _ : LogicalOp =>
     DecodeShift ('b"00") >>= fun shift_type : ShiftType =>
     execute_aarch64_instrs_integer_logical_shiftedreg
       30 64 false 1 0 LogicalOp_ORR false 0 shift_type).
Proof. unfold chez_word_0008. chain. Qed.

Lemma DecodeShift_LSL : DecodeShift ('b"00") = returnM ShiftType_LSL.
Proof. reflexivity. Qed.

(* +0x0c tst x30, #7  =  ANDS XZR, X30, #imm with N=1 imms=000010 immr=000000 *)
Theorem chez_000c_decode pc :
  __DecodeA64 pc chez_word_000c =
  SEE_guard 41
    (undefined_bool tt >>= fun _ : bool =>
     undefined_LogicalOp tt >>= fun _ : LogicalOp =>
     undefined_bitvector (__id 64) >>= fun _ : bits 64 =>
     DecodeBitMasks ('b"1") ('b"000010") ('b"000000") true 64 >>= fun '(imm, _) =>
     execute_aarch64_instrs_integer_logical_immediate 31 64 imm 30 LogicalOp_AND true).
Proof. unfold chez_word_000c. chain. Qed.

(* +0x10 b.ne +0x24 : cond 0b0001, offset 0x14 *)
Theorem chez_0010_decode pc :
  __DecodeA64 pc chez_word_0010 =
  SEE_guard 69
    (execute_aarch64_instrs_branch_conditional_cond ('b"0001") (Ox"0000000000000014")).
Proof. unfold chez_word_0010. chain. Qed.

(* +0x18 b.vs +0x24 : cond 0b0110, offset 0xc *)
Theorem chez_0018_decode pc :
  __DecodeA64 pc chez_word_0018 =
  SEE_guard 69
    (execute_aarch64_instrs_branch_conditional_cond ('b"0110") (Ox"000000000000000C")).
Proof. unfold chez_word_0018. chain. Qed.

(* +0x1c ldur x10, [x20]: 64-bit load, n=20, t=10, offset 0, tag-checked *)
Theorem chez_001c_decode pc :
  __DecodeA64 pc chez_word_001c =
  SEE_guard 680
    (undefined_MemOp tt >>= fun _ : MemOp =>
     undefined_bool tt >>= fun _ : bool =>
     undefined_Constraint tt >>= fun _ : Constraint =>
     execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
       64 MemOp_LOAD 20 false (Ox"0000000000000000") false 64 false false 10 true false false).
Proof. unfold chez_word_001c. chain. Qed.

(* +0x20 br x10: BranchType_INDIR, m=0, n=10, no PAC *)
Theorem chez_0020_decode pc :
  __DecodeA64 pc chez_word_0020 =
  SEE_guard 92
    (undefined_BranchType tt >>= fun _ : BranchType =>
     execute_aarch64_instrs_branch_unconditional_register BranchType_INDIR 0 10 false false true).
Proof. unfold chez_word_0020. chain. Qed.

(* +0x2c str x0, [x20, #8]: 64-bit store, n=20, t=0, offset 8, no writeback.
   The model routes STR (unsigned offset) to the shared post-index execute
   function with postindex = wback = false. *)
Theorem chez_002c_decode pc :
  __DecodeA64 pc chez_word_002c =
  SEE_guard 648
    (undefined_MemOp tt >>= fun _ : MemOp =>
     undefined_bool tt >>= fun _ : bool =>
     undefined_Constraint tt >>= fun _ : Constraint =>
     execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx
       64 MemOp_STORE 20 false (Ox"0000000000000008") false 64 false false 0 true false false).
Proof. unfold chez_word_002c. chain. Qed.

(* SBCL +0x210 ret (x30): BranchType_RET, n=30 *)
Theorem sbcl_0210_decode pc :
  __DecodeA64 pc sbcl_word_0210 =
  SEE_guard 94
    (undefined_BranchType tt >>= fun _ : BranchType =>
     execute_aarch64_instrs_branch_unconditional_register BranchType_RET 0 30 false false true).
Proof. unfold sbcl_word_0210. chain. Qed.

(* SBCL +0x2a0 blr x10: BranchType_INDCALL, n=10 *)
Theorem sbcl_02a0_decode pc :
  __DecodeA64 pc sbcl_word_02a0 =
  SEE_guard 90
    (undefined_BranchType tt >>= fun _ : BranchType =>
     execute_aarch64_instrs_branch_unconditional_register BranchType_INDCALL 0 10 false false true).
Proof. unfold sbcl_word_02a0. chain. Qed.

(* SBCL +0x264 brk #15: the decoder reads the FEAT_BTI bit of FeatureImpl,
   may set BTYPE compatibility, then executes the breakpoint with comment
   0x000f; the execute function is exactly AArch64_SoftwareBreakpoint. *)
Theorem sbcl_0264_decode pc :
  __DecodeA64 pc sbcl_word_0264 =
  SEE_guard 96
    (HaveBTIExt tt >>= fun w : bool =>
     (if w then SetBTypeCompatible true else returnM tt) >>
     execute_aarch64_instrs_system_exceptions_debug_breakpoint (Ox"000F")).
Proof. unfold sbcl_word_0264. chain. Qed.

Theorem sbcl_0264_execute :
  execute_aarch64_instrs_system_exceptions_debug_breakpoint (Ox"000F") =
  AArch64_SoftwareBreakpoint (Ox"000F").
Proof. reflexivity. Qed.

Theorem HaveBTIExt_reads_FeatureImpl :
  HaveBTIExt tt =
  (read_reg FeatureImpl >>= fun fi => returnM (vec_access_dec fi (num_of_Feature FEAT_BTI))).
Proof. reflexivity. Qed.

Print Assumptions chez_0000_decode.
Print Assumptions chez_0004_decode.
Print Assumptions chez_0008_decode.
Print Assumptions chez_000c_decode.
Print Assumptions chez_0010_decode.
Print Assumptions chez_0018_decode.
Print Assumptions chez_001c_decode.
Print Assumptions chez_0020_decode.
Print Assumptions chez_002c_decode.
Print Assumptions sbcl_0210_decode.
Print Assumptions sbcl_02a0_decode.
Print Assumptions sbcl_0264_decode.
Print Assumptions sbcl_0264_execute.
Print Assumptions HaveBTIExt_reads_FeatureImpl.
Print Assumptions DecodeShift_LSL.
