(* Shen/JIT Phase 0, AArch64 spike: what the sail-arm 7d058164 Coq model says
   about "store code, then fetch it".

   Not a scripts/prove module. Evidence kind of every theorem: model theorem
   (coq-sail 0.19 interface plus the model's own definitions).

   Result: the model's instruction monad has no memory state. A read, including
   an instruction fetch, is an event whose answer is unconstrained by earlier
   writes, so these theorems accept the OLD bytes and the NEW bytes alike.
   Barriers and cache operations are events with no register effect. A binary
   with cache maintenance and one without differ only in their event lists; the
   model alone gives those events no meaning. *)
Require Import SailStdpp.Base SailStdpp.ConcurrencyInterfaceTypes
  SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions.
Require Import BuriArm.BuriArmSeq.
Import Defs.
Open Scope Z.

Notation Req4 := (Interface.ReadReq.t 4%N).

(* The model's sail_mem_read is exactly one MemRead event. *)
Theorem sail_mem_read_is_one_event {n : Z}
  (req : Mem_read_request n _ _ _ _) :
  exists n' q k, (sail_mem_read req : M _) = Interface.Next (Interface.MemRead n' q) k.
Proof. do 3 eexists. reflexivity. Qed.

(* After any 4-byte write, any 4-byte read, whatever its access kind (so an
   instruction fetch of the same address too), may be answered with ANY bytes:
   both the bytes just written and the bytes that were there before. *)
Theorem read_after_write_unconstrained
  (w : Interface.WriteReq.t 4%N) (wres : option bool + _)
  (r : Req4) (answer : bv (8 * 4) * option bool + _) :
  Interface.iTrace_match
    (Interface.Next (Interface.MemWrite 4%N w) (fun _ =>
       Interface.Next (Interface.MemRead 4%N r) (fun v => Interface.Ret v))
      : Interface.iMon (fun _ : Type => exception) _)
    (cons (Interface.IEvent (Interface.MemWrite 4%N w) wres)
      (cons (Interface.IEvent (Interface.MemRead 4%N r) answer) nil), inl answer).
Proof. repeat constructor. Qed.

(* The sequential reading is no stricter: it carries registers only, so a read
   event takes any answer, and a write event leaves the state unchanged. *)
Theorem sexec_read_any {A} rs (r : Req4) k rs' (a : A) answer :
  sexec rs (k answer) rs' a ->
  sexec rs (Interface.Next (Interface.MemRead 4%N r) k) rs' a.
Proof. intros H. eapply SOther; [reflexivity | exact H]. Qed.

Theorem sexec_write_no_state {A} rs (w : Interface.WriteReq.t 4%N) k rs' (a : A) res :
  sexec rs (k res) rs' a ->
  sexec rs (Interface.Next (Interface.MemWrite 4%N w) k) rs' a.
Proof. intros H. eapply SOther; [reflexivity | exact H]. Qed.

(* ISB, DSB and every cache operation are one event and change no register. *)
Lemma sexec_one_event {T} rs (oc : Interface.outcome (fun _ : Type => exception) T) (v : T) :
  other_oc oc = true -> sexec rs (Interface.Next oc Interface.Ret) rs v.
Proof. intros H. eapply SOther; [exact H | constructor]. Qed.

Theorem isb_no_register_effect rs :
  sexec rs (InstructionSynchronizationBarrier tt) rs tt.
Proof. apply (sexec_one_event rs (Interface.Barrier _) tt). reflexivity. Qed.

Theorem dsb_no_register_effect rs d t x :
  sexec rs (DataSynchronizationBarrier d t x) rs tt.
Proof. apply (sexec_one_event rs (Interface.Barrier _) tt). reflexivity. Qed.

Theorem cache_op_no_register_effect rs c :
  sexec rs (CACHE_OP c) rs tt.
Proof. apply (sexec_one_event rs (Interface.CacheOp _) tt). reflexivity. Qed.

Print Assumptions sail_mem_read_is_one_event.
Print Assumptions read_after_write_unconstrained.
Print Assumptions sexec_read_any.
Print Assumptions sexec_write_no_state.
Print Assumptions isb_no_register_effect.
Print Assumptions dsb_no_register_effect.
Print Assumptions cache_op_no_register_effect.
