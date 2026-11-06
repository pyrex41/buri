(** * Rung 2 support: [copy_value]'s stack frame, its entry and exit paths, and the
    register-preservation vocabulary shared by every path through the function. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Definition at_off (a : word) (k : Z) : word := Z_to_bv 64 (bv_unsigned a + k).

Lemma u_at_off : forall a k, (0 <= bv_unsigned a + k < 2^64)%Z ->
  bv_unsigned (at_off a k) = (bv_unsigned a + k)%Z.
Proof. intros. unfold at_off. apply u_Z2bv; lia. Qed.

(** Registers a RISC-V callee must preserve and that no path here touches. *)
Definition kept (x : reg) : Prop :=
  x <> 1 /\ x <> 2 /\ x <> 5 /\ x <> 6 /\ x <> 7 /\ x <> 8 /\ x <> 9 /\
  x <> 10 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17 /\
  x <> 18 /\ x <> 19 /\ x <> 28 /\ x <> 29 /\ x <> 30 /\ x <> 31.

Ltac kept_frame :=
  let x := fresh "x" in let Hk := fresh "Hk" in
  intros x Hk; unfold kept in Hk; decompose [and] Hk;
  repeat (rewrite getr_other by assumption); reflexivity.

(** The saved registers in a frame at [fp]. *)
Definition framed (m : word -> option byte) (fp ra s0 s1 s2 s3 : word) : Prop :=
  wat m (at_off fp 40) ra /\ wat m (at_off fp 32) s0 /\ wat m (at_off fp 24) s1 /\
  wat m (at_off fp 16) s2 /\ wat m (at_off fp 8) s3.

Definition push_mem (mem : word -> option byte) (fp ra s0 s1 s2 s3 : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_off fp 40) (w8 ra)) (at_off fp 32) (w8 s0)) (at_off fp 24) (w8 s1))
    (at_off fp 16) (w8 s2)) (at_off fp 8) (w8 s3).

Definition stack_ok (sp : word) : Prop :=
  (TH <= bv_unsigned sp - 48)%Z /\ (bv_unsigned sp <= 2^63)%Z.

Section S.
Context {fx : FPState}.

Lemma push_framed : forall mem fp ra s0 s1 s2 s3,
  (bv_unsigned fp + 48 <= 2^63)%Z ->
  framed (push_mem mem fp ra s0 s1 s2 s3) fp ra s0 s1 s2 s3.
Proof.
  intros mem fp ra s0 s1 s2 s3 Hb. pose proof (bv_unsigned_in_range _ fp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr.
  assert (H8 : bv_unsigned (at_off fp 8) = (bv_unsigned fp + 8)%Z) by (apply u_at_off; lia).
  assert (H16 : bv_unsigned (at_off fp 16) = (bv_unsigned fp + 16)%Z) by (apply u_at_off; lia).
  assert (H24 : bv_unsigned (at_off fp 24) = (bv_unsigned fp + 24)%Z) by (apply u_at_off; lia).
  assert (H32 : bv_unsigned (at_off fp 32) = (bv_unsigned fp + 32)%Z) by (apply u_at_off; lia).
  assert (H40 : bv_unsigned (at_off fp 40) = (bv_unsigned fp + 40)%Z) by (apply u_at_off; lia).
  unfold framed, push_mem. repeat split;
    repeat (first [ apply wat_hit | apply wat_other ]; rewrite ?H8, ?H16, ?H24, ?H32, ?H40; try lia).
Qed.

Lemma push_clear : forall mem fp ra s0 s1 s2 s3,
  mem_clear mem TL TH -> (TH <= bv_unsigned fp)%Z -> (bv_unsigned fp + 48 <= 2^63)%Z ->
  mem_clear (push_mem mem fp ra s0 s1 s2 s3) TL TH.
Proof.
  intros mem fp ra s0 s1 s2 s3 Hc Ht Hb. pose proof (bv_unsigned_in_range _ fp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr.
  unfold push_mem.
  repeat apply clear_store; try assumption; rewrite u_at_off by lia; lia.
Qed.

Lemma push_grows : forall mem fp ra s0 s1 s2 s3,
  mem_grows mem (push_mem mem fp ra s0 s1 s2 s3).
Proof.
  intros mem fp ra s0 s1 s2 s3 x Hx. unfold push_mem.
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). exact Hx.
Qed.

Lemma push_outside : forall mem fp ra s0 s1 s2 s3 (a : word) n,
  (bv_unsigned fp + 48 <= 2^63)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned fp + 8 \/ bv_unsigned fp + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn source_segs (push_mem mem fp ra s0 s1 s2 s3) a n = rdn source_segs mem a n.
Proof.
  intros mem fp ra s0 s1 s2 s3 a n Hb Hd Ha. pose proof (bv_unsigned_in_range _ fp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr.
  assert (H1 : forall (m : word -> option byte) (v : word) k, (8 <= k <= 40)%Z ->
    rdn source_segs (wbytes m (at_off fp k) (w8 v)) a n = rdn source_segs m a n).
  { intros m v k Hk. apply rdn_wbytes_out; rewrite ?len_w8; cbn [Z.of_nat]; rewrite ?u_at_off by lia; lia. }
  unfold push_mem. rewrite !H1 by lia. reflexivity.
Qed.

(** Entry: six instructions. *)
Lemma cv_prologue : forall regs mem rom (sp : word),
  mem_clear mem TL TH ->
  getr regs 2 = sp -> stack_ok sp ->
  writable mem (bv_unsigned sp - 48) (bv_unsigned sp) ->
  msteps source_segs (mkst regs (0x11bc0 : word) mem rom)
    (mkst (regupd regs 2 (at_off sp (-48))) (0x11bcc : word)
       (push_mem mem (at_off sp (-48)) (getr regs 1) (getr regs 8) (getr regs 9)
                 (getr regs 18) (getr regs 19)) rom).
Proof.
  intros regs mem rom sp Hc Hsp [Hlo Hhi] Hw.
  pose proof (bv_unsigned_in_range _ sp) as Hr.
  change (bv_modulus 64) with (2^64)%Z in Hr. unfold TH in Hlo.
  set (fp := at_off sp (-48)).
  assert (Hfp : bv_unsigned fp = (bv_unsigned sp - 48)%Z) by (apply u_at_off; lia).
  assert (Ho : forall k, (0 <= k <= 48)%Z -> bv_unsigned (at_off fp k) = (bv_unsigned sp - 48 + k)%Z).
  { intros k Hk. rewrite u_at_off by lia. lia. }
  assert (Hadr : forall k, v_addi fp k = at_off fp k) by reflexivity.
  assert (Hcl : forall (m : word -> option byte) (v : word) k, mem_clear m TL TH -> (0 <= k <= 40)%Z ->
     mem_clear (wbytes m (at_off fp k) (w8 v)) TL TH).
  { intros m v k Hm Hk. apply clear_store; [exact Hm|rewrite Ho by lia; unfold TH; lia|rewrite Ho by lia; lia]. }
  assert (Hst : forall (m : word -> option byte) k, writable m (bv_unsigned sp - 48) (bv_unsigned sp) -> (0 <= k <= 40)%Z ->
     store_ok source_segs m (at_off fp k) 8%nat = true).
  { intros m k Hm Hk. eapply writable_store_ok; [exact Hm| | |]; rewrite ?Ho by lia; cbn [Z.of_nat]; lia. }
  norm_pc.
  wsv Hc SF_11bc0 SD_11bc0 fp ltac:(rewrite Hsp; reflexivity).
  wsd Hc SF_11bc2 SD_11bc2 (at_off fp 40) (getr regs 1) ltac:(rewrite Hadr; reflexivity) ltac:(apply Hst; [exact Hw|lia]).
  assert (Hc1 := Hcl mem (getr regs 1) 40%Z Hc ltac:(lia)).
  assert (Hw1 := writable_store mem _ _ (at_off fp 40) (w8 (getr regs 1)) Hw).
  wsd Hc1 SF_11bc4 SD_11bc4 (at_off fp 32) (getr regs 8) ltac:(rewrite Hadr; reflexivity) ltac:(apply Hst; [exact Hw1|lia]).
  assert (Hc2 := Hcl _ (getr regs 8) 32%Z Hc1 ltac:(lia)).
  assert (Hw2 := writable_store _ _ _ (at_off fp 32) (w8 (getr regs 8)) Hw1).
  wsd Hc2 SF_11bc6 SD_11bc6 (at_off fp 24) (getr regs 9) ltac:(rewrite Hadr; reflexivity) ltac:(apply Hst; [exact Hw2|lia]).
  assert (Hc3 := Hcl _ (getr regs 9) 24%Z Hc2 ltac:(lia)).
  assert (Hw3 := writable_store _ _ _ (at_off fp 24) (w8 (getr regs 9)) Hw2).
  wsd Hc3 SF_11bc8 SD_11bc8 (at_off fp 16) (getr regs 18) ltac:(rewrite Hadr; reflexivity) ltac:(apply Hst; [exact Hw3|lia]).
  assert (Hc4 := Hcl _ (getr regs 18) 16%Z Hc3 ltac:(lia)).
  assert (Hw4 := writable_store _ _ _ (at_off fp 16) (w8 (getr regs 18)) Hw3).
  wsd Hc4 SF_11bca SD_11bca (at_off fp 8) (getr regs 19) ltac:(rewrite Hadr; reflexivity) ltac:(apply Hst; [exact Hw4|lia]).
  unfold push_mem. apply mst_refl.
Qed.

End S.
