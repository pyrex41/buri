(** * Words in memory, writable ranges, and the store tactic.  Proof-side only. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.

Abbreviation w8 v := (word_to_le_bytes 8 v).

(** [a] holds the 64-bit value [v], little-endian. *)
Definition wat (m : word -> option byte) (a v : word) : Prop :=
  rdn source_segs m a 8%nat = Some (w8 v).

(** Every byte of [lo, hi) can be stored to. *)
Definition writable (m : word -> option byte) (lo hi : Z) : Prop :=
  forall a : word, lo <= bv_unsigned a < hi -> wview source_segs m a <> None.

Lemma len_w8 : forall v : word, length (w8 v) = 8%nat.
Proof. intros. apply length_word_to_le_bytes. Qed.

Lemma writable_store_ok : forall m lo hi (a : word) (n : nat),
  writable m lo hi -> lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= hi -> hi <= 2^64 ->
  store_ok source_segs m a n = true.
Proof.
  intros m lo hi a n Hw. revert a. induction n as [|n IH]; intros a Hlo Hhi Hh; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hhi. cbn [store_ok].
  destruct (wview source_segs m a) as [b|] eqn:Hv.
  - destruct n as [|n']; [reflexivity|].
    pose proof (bv_unsigned_in_range _ a) as Hr. change (bv_modulus 64) with (2^64) in Hr.
    assert (Hu : bv_unsigned (a + 1) = bv_unsigned a + 1).
    { rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1.
      apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. }
    apply IH; rewrite ?Hu; lia.
  - exfalso. apply (Hw a); [lia|exact Hv].
Qed.

Lemma writable_grows : forall m m' lo hi,
  mem_grows m m' -> writable m lo hi -> writable m' lo hi.
Proof. intros m m' lo hi Hg Hw a Ha. eapply wview_grows; [exact Hg|apply Hw; exact Ha]. Qed.

Lemma writable_store : forall m lo hi a bs,
  writable m lo hi -> writable (wbytes m a bs) lo hi.
Proof. intros. eapply writable_grows; [apply wbytes_grows|eassumption]. Qed.

Lemma wat_hit : forall m (a v : word), bv_unsigned a + 8 <= 2^64 ->
  wat (wbytes m a (w8 v)) a v.
Proof. intros. unfold wat. apply rdn_wbytes_hit8. exact H. Qed.

Lemma wat_other : forall m (a b v x : word),
  wat m b x ->
  bv_unsigned b + 8 <= bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned b ->
  bv_unsigned a + 8 <= 2^64 -> bv_unsigned b + 8 <= 2^64 ->
  wat (wbytes m a (w8 v)) b x.
Proof.
  intros m a b v x Hx Hd Ha Hb. unfold wat in *.
  rewrite rdn_wbytes_out; [exact Hx| | |]; rewrite ?len_w8; cbn [Z.of_nat]; lia.
Qed.

Lemma clear_store : forall m (a v : word),
  mem_clear m TL TH -> TH <= bv_unsigned a -> bv_unsigned a + 8 <= 2^64 ->
  mem_clear (wbytes m a (w8 v)) TL TH.
Proof.
  intros. apply mem_clear_wbytes; [assumption| |]; rewrite ?len_w8; cbn [Z.of_nat]; lia.
Qed.

Lemma bytes8 : forall v : word, bytes_le_to_Z (w8 v) = bv_unsigned v.
Proof. exact bytes_le_to_Z_8. Qed.

(* A load of [vv] at the address [aa], from a [wat] fact. *)
Ltac wld Hc F D aa vv addrprf Hw :=
  eapply mst_step;
  [ reflexivity
  | eapply z_ld_at with (a := aa) (v := vv) (bs := w8 vv);
    [ wxf_with Hc F | reflexivity | exact D | reflexivity
    | gres; imm_norm; addrprf
    | exact Hw
    | apply bytes8 ]
  | norm_pc ].
