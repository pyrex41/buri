(** * jit-write-run: every-input theorem in Theorem's unmodified process model.

    For every valid process input, argument, stack placement and launch: the binary
    that generates and runs its own code has the same observable behavior as an
    ordinary binary with immutable code that exits 42. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_defs jit_write_run_ns_source jit_write_run_ns_target.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import jit_write_run_ns_code.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.jit_write_run_ns Require Import TargetMemImage.

Import ListNotations.
Open Scope bv_scope.

Theorem omni_strong_universal :
  omni_strong_universal_T
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof.
  intros [sp_source brk_source mb_source rnd_source] [sp_target brk_target mb_target rnd_target]
    inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hspr & _). destruct Hent as (Hspa & _).
  destruct Hvalid as (Hva & Hve & _).
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  apply (cat_omni_strong_equiv_te
           source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
           target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
           [] (Z_to_bv 64 42) inp).
  - rewrite source_init_pc_val.
    apply source_wexit; assumption.
  - rewrite target_init_pc_val.
    apply target_wexit; assumption.
  - unfold bufs_modeled. constructor.
Qed.

Theorem strong_universal :
  strong_universal_T
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof. apply strong_universal_iff. exact omni_strong_universal. Qed.
