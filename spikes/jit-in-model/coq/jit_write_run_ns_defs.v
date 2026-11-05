(** * jit-write-run: shared definitions and image facts (Shen/JIT Phase 0, spike 1).

    The source writes two instruction words into its writable and executable
    segment, runs fence.i, calls them, and exits with their result.  The target is
    an ordinary binary with immutable code that exits 42. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_code.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x10078%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x11000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma source_no_ro_exec : no_ro_exec source_segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_wseg : wseg_ok source_segs (0x10000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x10000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x11000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x10000%Z) (hi := 0x11000%Z);
    [ | | | exact source_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.
