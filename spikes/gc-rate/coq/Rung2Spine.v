(** * Rung 2: the list-spine loop in [copy_value] (0x11d7a), proved by induction over a
    relation that follows the C loop, and the pair path that enters it.

    The loop keeps copying while the tail is a pair in from-space not yet forwarded. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung1ObjWords Rung2Frame Rung2Paths Rung2Pointer Rung2ObjSize.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
Set Default Timeout 40.

Lemma eq_true : forall a b : word, a = b -> branch_taken BC_EQ a b = true.
Proof. intros a b ->. cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma eq_false : forall a b : word, bv_unsigned a <> bv_unsigned b ->
  branch_taken BC_EQ a b = false.
Proof. intros. cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.

Lemma geu_true : forall a b : word, (bv_unsigned b <= bv_unsigned a)%Z ->
  branch_taken BC_GEU a b = true.
Proof.
  intros. cbn [branch_taken]. unfold bv_ltu.
  rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma geu_false : forall a b : word, (bv_unsigned a < bv_unsigned b)%Z ->
  branch_taken BC_GEU a b = false.
Proof.
  intros. cbn [branch_taken]. unfold bv_ltu.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Section Layout.
Context {fx : FPState}.

(* The collector's regions.  [c] is the Copy struct in the caller's frame, above this
   function's frame; both semispaces lie below the stack and are disjoint. *)
Variables (rom : word -> option byte) (c from fw q0 tohi fp ra s0 s1 s2 s3 : word).
Let fromhi : Z := (bv_unsigned from + 8 * bv_unsigned fw)%Z.
Hypothesis Hfl : (TH <= bv_unsigned from)%Z.
Hypothesis Htl : (TH <= bv_unsigned q0 <= bv_unsigned tohi)%Z.
Hypothesis Hdis : (bv_unsigned tohi <= bv_unsigned from \/ fromhi <= bv_unsigned q0)%Z.
Hypothesis Hfs : (fromhi <= bv_unsigned fp)%Z.
Hypothesis Hsp8 : (TH <= bv_unsigned fp)%Z.
Hypothesis Hts : (bv_unsigned tohi <= bv_unsigned fp)%Z.
Hypothesis Hfc : (bv_unsigned fp + 48 <= bv_unsigned c)%Z.
Hypothesis Hch : (bv_unsigned c + 56 <= 2^63)%Z.

(** What holds of memory at every point in the function. *)
Definition minv (m : word -> option byte) : Prop :=
  mem_clear m TL TH /\
  writable m (bv_unsigned from) fromhi /\
  writable m (bv_unsigned q0) (bv_unsigned tohi) /\
  writable m (bv_unsigned c) (bv_unsigned c + 24) /\
  wat m c from /\ wat m (at_off c 8) fw /\
  framed m fp ra s0 s1 s2 s3.

Definition in_heap (a : Z) : Prop :=
  ((bv_unsigned from <= a /\ a + 8 <= fromhi) \/
   (bv_unsigned q0 <= a /\ a + 8 <= bv_unsigned tohi))%Z.

Lemma ranges :
  (0 <= bv_unsigned fp /\ bv_unsigned fp + 48 <= 2^63 /\ bv_unsigned tohi <= 2^63 /\ fromhi <= 2^63)%Z.
Proof.
  pose proof (bv_unsigned_in_range _ fp) as Hr. change (bv_modulus 64) with (2^64)%Z in Hr. lia.
Qed.

Lemma framed_store : forall m (a v : word),
  framed m fp ra s0 s1 s2 s3 ->
  (bv_unsigned a + 8 <= bv_unsigned fp + 8 \/ bv_unsigned fp + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= 2^64)%Z ->
  framed (wbytes m a (w8 v)) fp ra s0 s1 s2 s3.
Proof.
  intros m a v [H1 [H2 [H3 [H4 H5]]]] Hd Ha. pose proof ranges as (R0 & R1 & _).
  unfold framed. split; [|split; [|split; [|split]]]; (apply wat_other; [assumption | rewrite u_at_off by lia; lia | exact Ha | rewrite u_at_off by lia; lia]).
Qed.

Lemma minv_heap : forall m (a v : word),
  minv m -> in_heap (bv_unsigned a) -> minv (wbytes m a (w8 v)).
Proof.
  intros m a v [Hc [W1 [W2 [W3 [A1 [A2 F]]]]]] Hh. pose proof ranges as (R0 & R1 & R2 & R3).
  assert (Hr : (0 <= bv_unsigned c)%Z) by lia.
  assert (Ha : (TH <= bv_unsigned a /\ bv_unsigned a + 8 <= bv_unsigned fp)%Z)
    by (unfold in_heap in Hh; lia).
  unfold minv. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply clear_store; [exact Hc|lia|lia].
  - apply writable_store; exact W1.
  - apply writable_store; exact W2.
  - apply writable_store; exact W3.
  - apply wat_other; [exact A1|lia|lia|lia].
  - apply wat_other; [exact A2|rewrite u_at_off by lia; lia|lia|rewrite u_at_off by lia; lia].
  - apply framed_store; [exact F|lia|lia].
Qed.

(** The store of c->next, at c+16: the words at c and c+8 are untouched. *)
Lemma minv_next : forall m (v : word), minv m -> minv (wbytes m (at_off c 16) (w8 v)).
Proof.
  intros m v [Hc [W1 [W2 [W3 [A1 [A2 F]]]]]]. pose proof ranges as (R0 & R1 & R2 & R3).
  assert (H16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  unfold minv. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply clear_store; [exact Hc|rewrite H16; lia|rewrite H16; lia].
  - apply writable_store; exact W1.
  - apply writable_store; exact W2.
  - apply writable_store; exact W3.
  - apply wat_other; [exact A1|rewrite H16; lia|rewrite H16; lia|lia].
  - apply wat_other; [exact A2|rewrite H16, u_at_off by lia; lia|rewrite H16; lia|rewrite u_at_off by lia; lia].
  - apply framed_store; [exact F|rewrite H16; lia|rewrite H16; lia].
Qed.

Lemma heap_store_ok : forall m (a : word),
  minv m -> in_heap (bv_unsigned a) -> store_ok source_segs m a 8%nat = true.
Proof.
  intros m a [_ [W1 [W2 _]]] Hh. pose proof ranges as (R0 & R1 & R2 & R3).
  destruct Hh as [Hh|Hh].
  - eapply writable_store_ok; [exact W1|lia|cbn [Z.of_nat]; lia|lia].
  - eapply writable_store_ok; [exact W2|lia|cbn [Z.of_nat]; lia|lia].
Qed.

Lemma next_store_ok : forall m, minv m -> store_ok source_segs m (at_off c 16) 8%nat = true.
Proof.
  intros m [_ [_ [_ [W3 _]]]]. pose proof ranges as (R0 & R1 & R2 & R3).
  assert (H16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  eapply writable_store_ok; [exact W3|rewrite H16; lia|rewrite H16; cbn [Z.of_nat]; lia|lia].
Qed.

(** One iteration's memory writes, in the machine's order. *)
Definition spine_write (m : word -> option byte) (cur p w0 w1 : word) :=
  let cq := at_off cur 8 in
  wbytes (wbytes (wbytes (wbytes (wbytes m cur (w8 w0)) cq (w8 w1))
    p (w8 V_FORWARD)) (at_off p 8) (w8 (v_ori cur 3))) (at_off c 16) (w8 (at_off cur 16)).

(** The loop as a relation: [spine m cur t m' cur'] says that from memory [m], with the
    to-space cursor at [cur] and pair-tagged tail [t], the C loop ends in [m'] and [cur']. *)
Inductive spine : (word -> option byte) -> word -> word -> (word -> option byte) -> word -> Prop :=
| spine_low : forall m cur t,
    (bv_unsigned (ptr_of t) < bv_unsigned from)%Z ->
    spine m cur t m cur
| spine_high : forall m cur t,
    (fromhi <= bv_unsigned (ptr_of t))%Z ->
    spine m cur t m cur
| spine_fwd : forall m cur t,
    (bv_unsigned from <= bv_unsigned (ptr_of t) < fromhi)%Z ->
    wat m (ptr_of t) V_FORWARD ->
    spine m cur t m cur
| spine_last : forall m cur t w0 w1,
    (bv_unsigned from <= bv_unsigned (ptr_of t))%Z -> (bv_unsigned (ptr_of t) + 16 <= fromhi)%Z ->
    wat m (ptr_of t) w0 -> w0 <> V_FORWARD -> wat m (at_off (ptr_of t) 8) w1 ->
    (bv_unsigned q0 <= bv_unsigned cur)%Z -> (bv_unsigned cur + 16 <= bv_unsigned tohi)%Z ->
    tag w1 <> 3%Z ->
    spine m cur t (spine_write m cur (ptr_of t) w0 w1) (at_off cur 16)
| spine_more : forall m cur t w0 w1 m' cur',
    (bv_unsigned from <= bv_unsigned (ptr_of t))%Z -> (bv_unsigned (ptr_of t) + 16 <= fromhi)%Z ->
    wat m (ptr_of t) w0 -> w0 <> V_FORWARD -> wat m (at_off (ptr_of t) 8) w1 ->
    (bv_unsigned q0 <= bv_unsigned cur)%Z -> (bv_unsigned cur + 16 <= bv_unsigned tohi)%Z ->
    tag w1 = 3%Z ->
    spine (spine_write m cur (ptr_of t) w0 w1) (at_off cur 16) w1 m' cur' ->
    spine m cur t m' cur'.

Definition spine_regs (R : bvmap 5 word) (cur t : word) : Prop :=
  getr R 10 = c /\ getr R 13 = from /\ getr R 14 = V_FORWARD /\ getr R 15 = cur /\
  getr R 8 = cur /\ getr R 9 = t /\ getr R 16 = Z_to_bv 64 3.

Definition spine_post (R R2 : bvmap 5 word) : Prop :=
  getr R2 10 = getr R 10 /\ getr R2 11 = getr R 11 /\ getr R2 2 = getr R 2 /\
  (forall x : reg, kept x -> getr R2 x = getr R x).

Lemma minv_spine_write : forall m (cur p w0 w1 : word),
  minv m ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  (bv_unsigned q0 <= bv_unsigned cur)%Z -> (bv_unsigned cur + 16 <= bv_unsigned tohi)%Z ->
  minv (spine_write m cur p w0 w1).
Proof.
  intros m cur p w0 w1 I Hp1 Hp2 Hq1 Hq2. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ cur) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  unfold spine_write. apply minv_next.
  apply minv_heap; [apply minv_heap; [apply minv_heap; [apply minv_heap; [exact I|]|]|]|].
  - right. lia.
  - right. rewrite u_at_off by lia. lia.
  - left. lia.
  - left. rewrite u_at_off by lia. lia.
Qed.

Lemma word_ne : forall a b : word, a <> b -> bv_unsigned a <> bv_unsigned b.
Proof. intros a b Hn He. apply Hn. apply bv_eq. exact He. Qed.

(** One iteration, from the top of the loop to its last branch. *)
Lemma spine_iter : forall m cur t w0 w1 R,
  minv m -> spine_regs R cur t ->
  (bv_unsigned from <= bv_unsigned (ptr_of t))%Z -> (bv_unsigned (ptr_of t) + 16 <= fromhi)%Z ->
  wat m (ptr_of t) w0 -> w0 <> V_FORWARD -> wat m (at_off (ptr_of t) 8) w1 ->
  (bv_unsigned q0 <= bv_unsigned cur)%Z -> (bv_unsigned cur + 16 <= bv_unsigned tohi)%Z ->
  exists Rx,
    msteps source_segs (mkst R (0x11d7a : word) m rom)
      (mkst Rx (0x11daa : word) (spine_write m cur (ptr_of t) w0 w1) rom) /\
    getr Rx 12 = Z_to_bv 64 (tag w1) /\
    spine_regs Rx (at_off cur 16) w1 /\ spine_post R Rx.
Proof.
  intros m cur t w0 w1 R I [A10 [A13 [A14 [A15 [A8 [A9 A16]]]]]] Hp1 Hp2 H0 Hne H1 Hq1 Hq2.
  pose proof ranges as (R0 & R1 & R2 & R3).
  set (p := ptr_of t) in *.
  pose proof (bv_unsigned_in_range _ cur) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  assert (Ucq : bv_unsigned (at_off cur 8) = (bv_unsigned cur + 8)%Z) by (apply u_at_off; lia).
  assert (Up8 : bv_unsigned (at_off p 8) = (bv_unsigned p + 8)%Z) by (apply u_at_off; lia).
  assert (Hadd : v_add (v_slli fw 3) from = Z_to_bv 64 fromhi).
  { pose proof (bv_unsigned_in_range _ fw) as Rw. pose proof (bv_unsigned_in_range _ from) as Rf.
    change (bv_modulus 64) with (2^64)%Z in Rw, Rf.
    unfold v_add, v_slli, fromhi. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite u_Z2bv by (unfold fromhi in *; lia). f_equal. change (2^3)%Z with 8%Z. lia. }
  set (m1 := wbytes m cur (w8 w0)).
  assert (I1 : minv m1) by (apply minv_heap; [exact I|right; lia]).
  assert (W1 : wat m1 (at_off p 8) w1)
    by (apply wat_other; [exact H1|rewrite Up8; unfold fromhi in *; lia|lia|rewrite Up8; lia]).
  set (m2 := wbytes m1 (at_off cur 8) (w8 w1)).
  assert (I2 : minv m2) by (apply minv_heap; [exact I1|right; rewrite Ucq; lia]).
  set (m3 := wbytes m2 p (w8 V_FORWARD)).
  assert (I3 : minv m3) by (apply minv_heap; [exact I2|left; lia]).
  set (m4 := wbytes m3 (at_off p 8) (w8 (v_ori cur 3))).
  assert (I4 : minv m4) by (apply minv_heap; [exact I3|left; rewrite Up8; lia]).
  assert (W2 : wat m4 (at_off cur 8) w1).
  { apply wat_other; [apply wat_other; [apply wat_hit; rewrite Ucq; lia
      |rewrite Ucq; unfold fromhi in *; lia|lia|rewrite Ucq; lia]
      |rewrite Ucq, Up8; unfold fromhi in *; lia|rewrite Up8; lia|rewrite Ucq; lia]. }
  pose proof I as [Hc [_ [_ [_ [_ [Hfw _]]]]]].
  eexists. split.
  - wsv Hc SF_11d7a SD_11d7a p ltac:(rewrite A9; reflexivity).
    wbr_ft Hc SF_11d7c SD_11d7c ltac:(rewrite A13; apply ltu_false; lia).
    wld Hc SF_11d80 SD_11d80 (at_off c 8) fw ltac:(rewrite A10; reflexivity) Hfw.
    ws Hc SF_11d82 SD_11d82.
    wsv Hc SF_11d84 SD_11d84 (Z_to_bv 64 fromhi) ltac:(rewrite A13; exact Hadd).
    wbr_ft Hc SF_11d86 SD_11d86 ltac:(apply geu_false; rewrite u_Z2bv by (unfold fromhi in *; lia); lia).
    wld Hc SF_11d8a SD_11d8a p w0 ltac:(apply v_addi_zero) H0.
    wbr_ft Hc SF_11d8c SD_11d8c ltac:(rewrite A14; apply eq_false, word_ne; exact Hne).
    wsd Hc SF_11d90 SD_11d90 cur w0 ltac:(rewrite A15; apply v_addi_zero)
      ltac:(apply heap_store_ok; [exact I|right; lia]).
    wld (proj1 I1) SF_11d92 SD_11d92 (at_off p 8) w1 ltac:(reflexivity) W1.
    wsd (proj1 I1) SF_11d94 SD_11d94 (at_off cur 8) w1 ltac:(rewrite A15; reflexivity)
      ltac:(apply heap_store_ok; [exact I1|right; rewrite Ucq; lia]).
    wsd (proj1 I2) SF_11d96 SD_11d96 p V_FORWARD ltac:(apply v_addi_zero)
      ltac:(apply heap_store_ok; [exact I2|left; lia]).
    wsv (proj1 I3) SF_11d98 SD_11d98 (v_ori cur 3) ltac:(rewrite A8; reflexivity).
    wsd (proj1 I3) SF_11d9c SD_11d9c (at_off p 8) (v_ori cur 3) ltac:(reflexivity)
      ltac:(apply heap_store_ok; [exact I3|left; rewrite Up8; lia]).
    wld (proj1 I4) SF_11d9e SD_11d9e (at_off cur 8) w1 ltac:(rewrite A15; reflexivity) W2.
    wsv (proj1 I4) SF_11da0 SD_11da0 (at_off cur 16) ltac:(rewrite A15; reflexivity).
    wsd (proj1 I4) SF_11da2 SD_11da2 (at_off c 16) (at_off cur 16) ltac:(rewrite A10; reflexivity)
      ltac:(apply next_store_ok; exact I4).
    pose proof (proj1 (minv_next _ (at_off cur 16) I4)) as Hc5.
    wsv Hc5 SF_11da4 SD_11da4 (Z_to_bv 64 (tag w1)) ltac:(apply andi7).
    wsv Hc5 SF_11da8 SD_11da8 (at_off cur 16) ltac:(rewrite A8; reflexivity).
    unfold spine_write. apply mst_refl.
  - gres. split; [reflexivity|]. split.
    + unfold spine_regs. gres. repeat split; assumption.
    + unfold spine_post. gres. repeat split; [reflexivity .. | kept_frame].
Qed.

(** THEOREM: the loop does exactly what the relation says, and keeps the invariant. *)
Lemma spine_loop : forall m cur t m' cur',
  spine m cur t m' cur' ->
  forall R, minv m -> spine_regs R cur t ->
  exists R2,
    msteps source_segs (mkst R (0x11d7a : word) m rom) (mkst R2 (0x11dae : word) m' rom) /\
    spine_post R R2 /\ minv m'.
Proof.
  assert (Hadd : v_add (v_slli fw 3) from = Z_to_bv 64 fromhi).
  { pose proof ranges as (R0 & R1 & R2 & R3).
    pose proof (bv_unsigned_in_range _ fw) as Rw. pose proof (bv_unsigned_in_range _ from) as Rf.
    change (bv_modulus 64) with (2^64)%Z in Rw, Rf.
    unfold v_add, v_slli, fromhi. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite u_Z2bv by (unfold fromhi in *; lia). f_equal. change (2^3)%Z with 8%Z. lia. }
  pose proof ranges as (R0 & R1 & R2 & R3).
  assert (Ufh : bv_unsigned (Z_to_bv 64 fromhi) = fromhi).
  { pose proof (bv_unsigned_in_range _ fw) as Rw. pose proof (bv_unsigned_in_range _ from) as Rf.
    change (bv_modulus 64) with (2^64)%Z in Rw, Rf.
    apply u_Z2bv; unfold fromhi in *; lia. }
  induction 1; intros R I Hr; pose proof I as [Hc [_ [_ [_ [_ [Hfw _]]]]]];
    pose proof Hr as [A10 [A13 [A14 [A15 [A8 [A9 A16]]]]]].
  - eexists. split; [|split; [|exact I]].
    + wsv Hc SF_11d7a SD_11d7a (ptr_of t) ltac:(rewrite A9; reflexivity).
      wbr_tk Hc SF_11d7c SD_11d7c ltac:(rewrite A13; apply ltu_true; exact H).
      apply mst_refl.
    + unfold spine_post. gres. repeat split; [kept_frame].
  - eexists. split; [|split; [|exact I]].
    + wsv Hc SF_11d7a SD_11d7a (ptr_of t) ltac:(rewrite A9; reflexivity).
      wbr_ft Hc SF_11d7c SD_11d7c ltac:(rewrite A13; apply ltu_false; unfold fromhi in *; 
        pose proof (bv_unsigned_in_range _ fw) as Rw; change (bv_modulus 64) with (2^64)%Z in Rw; lia).
      wld Hc SF_11d80 SD_11d80 (at_off c 8) fw ltac:(rewrite A10; reflexivity) Hfw.
      ws Hc SF_11d82 SD_11d82.
      wsv Hc SF_11d84 SD_11d84 (Z_to_bv 64 fromhi) ltac:(rewrite A13; exact Hadd).
      wbr_tk Hc SF_11d86 SD_11d86 ltac:(apply geu_true; rewrite Ufh; exact H).
      apply mst_refl.
    + unfold spine_post. gres. repeat split; [kept_frame].
  - destruct H as [H1 H2]. eexists. split; [|split; [|exact I]].
    + wsv Hc SF_11d7a SD_11d7a (ptr_of t) ltac:(rewrite A9; reflexivity).
      wbr_ft Hc SF_11d7c SD_11d7c ltac:(rewrite A13; apply ltu_false; lia).
      wld Hc SF_11d80 SD_11d80 (at_off c 8) fw ltac:(rewrite A10; reflexivity) Hfw.
      ws Hc SF_11d82 SD_11d82.
      wsv Hc SF_11d84 SD_11d84 (Z_to_bv 64 fromhi) ltac:(rewrite A13; exact Hadd).
      wbr_ft Hc SF_11d86 SD_11d86 ltac:(apply geu_false; rewrite Ufh; exact H2).
      wld Hc SF_11d8a SD_11d8a (ptr_of t) V_FORWARD ltac:(apply v_addi_zero) H0.
      wbr_tk Hc SF_11d8c SD_11d8c ltac:(rewrite A14; apply eq_true; reflexivity).
      apply mst_refl.
    + unfold spine_post. gres. repeat split; [kept_frame].
  - destruct (spine_iter m cur t w0 w1 R I Hr H H0 H1 H2 H3 H4 H5) as (Rx & Hm & A12 & Hrx & Hpx).
    pose proof (minv_spine_write m cur (ptr_of t) w0 w1 I H H0 H4 H5) as I2.
    pose proof Hrx as [_ [_ [_ [_ [_ [_ B16]]]]]].
    eexists. split; [|split; [|exact I2]].
    + eapply msteps_trans; [exact Hm|].
      wbr_ft (proj1 I2) SF_11daa SD_11daa ltac:(rewrite A12, B16; apply eq_false; rewrite !u_Z2bv by (pose proof (tag_range w1); lia); exact H6).
      apply mst_refl.
    + destruct Hpx as [P10 [P11 [P2 Pk]]]. unfold spine_post. repeat split; try assumption.
  - destruct (spine_iter m cur t w0 w1 R I Hr H H0 H1 H2 H3 H4 H5) as (Rx & Hm & A12 & Hrx & Hpx).
    pose proof (minv_spine_write m cur (ptr_of t) w0 w1 I H H0 H4 H5) as I2.
    pose proof Hrx as [_ [_ [_ [_ [_ [_ B16]]]]]].
    assert (Hb : msteps source_segs (mkst Rx (0x11daa : word) (spine_write m cur (ptr_of t) w0 w1) rom)
                   (mkst Rx (0x11d7a : word) (spine_write m cur (ptr_of t) w0 w1) rom)).
    { wbr_tk (proj1 I2) SF_11daa SD_11daa ltac:(rewrite A12, B16, H6; apply eq_true; reflexivity).
      apply mst_refl. }
    destruct (IHspine Rx I2 Hrx) as (Rf & Hm2 & Hp2 & I3).
    exists Rf. split; [|split; [|exact I3]].
    + eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hb|exact Hm2].
    + destruct Hpx as [P10 [P11 [P2 Pk]]]. destruct Hp2 as [Q10 [Q11 [Q2 Qk]]].
      unfold spine_post. rewrite Q10, Q11, Q2. repeat split; try assumption.
      intros x Hx. rewrite Qk, Pk by exact Hx. reflexivity.
Qed.

(** The next-pointer word tracks the cursor through the loop. *)
Lemma spine_next : forall m cur t m' cur',
  spine m cur t m' cur' -> wat m (at_off c 16) cur -> wat m' (at_off c 16) cur'.
Proof.
  pose proof ranges as (R0 & R1 & R2 & R3).
  assert (H16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  induction 1; intros Hw; try exact Hw.
  - unfold spine_write. apply wat_hit. rewrite H16; lia.
  - apply IHspine. unfold spine_write. apply wat_hit. rewrite H16; lia.
Qed.

(** Bytes outside both semispaces and c->next don't change. *)
Definition outside (a : word) (n : nat) : Prop :=
  (bv_unsigned a + Z.of_nat n <= bv_unsigned from \/ fromhi <= bv_unsigned a)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned q0 \/ bv_unsigned tohi <= bv_unsigned a)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned c + 16 \/ bv_unsigned c + 24 <= bv_unsigned a)%Z /\
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z.

Lemma store_outside : forall m (x v a : word) n,
  outside a n -> (in_heap (bv_unsigned x) \/ x = at_off c 16) ->
  rdn source_segs (wbytes m x (w8 v)) a n = rdn source_segs m a n.
Proof.
  intros m x v a n [O1 [O2 [O3 O4]]] Hx. pose proof ranges as (R0 & R1 & R2 & R3).
  assert (H16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  apply rdn_wbytes_out; rewrite ?len_w8; cbn [Z.of_nat]; try exact O4.
  - destruct Hx as [Hx| ->]; [unfold in_heap in Hx; lia|rewrite H16; lia].
  - destruct Hx as [Hx| ->]; [unfold in_heap in Hx; lia|rewrite H16; lia].
Qed.

Lemma write_outside : forall m cur p w0 w1 a n,
  outside a n ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  (bv_unsigned q0 <= bv_unsigned cur)%Z -> (bv_unsigned cur + 16 <= bv_unsigned tohi)%Z ->
  rdn source_segs (spine_write m cur p w0 w1) a n = rdn source_segs m a n.
Proof.
  intros m cur p w0 w1 a n O Hp1 Hp2 Hq1 Hq2. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ cur) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  unfold spine_write.
  rewrite store_outside by (exact O || (right; reflexivity)).
  rewrite store_outside; [|exact O|left; left; rewrite u_at_off by lia; lia].
  rewrite store_outside; [|exact O|left; left; lia].
  rewrite store_outside; [|exact O|left; right; rewrite u_at_off by lia; lia].
  rewrite store_outside; [reflexivity|exact O|left; right; lia].
Qed.

Lemma spine_outside : forall m cur t m' cur' a n,
  spine m cur t m' cur' -> outside a n ->
  rdn source_segs m' a n = rdn source_segs m a n.
Proof.
  intros m cur t m' cur' a n Hs O. induction Hs; try reflexivity.
  - apply write_outside; assumption.
  - rewrite IHHs. apply write_outside; assumption.
Qed.

Lemma spine_minv : forall m cur t m' cur', spine m cur t m' cur' -> minv m -> minv m'.
Proof.
  induction 1; intros I; try exact I.
  - apply minv_spine_write; assumption.
  - apply IHspine, minv_spine_write; assumption.
Qed.

(** Forwarded path, from the test to the exit. *)
Lemma body_forwarded : forall m R (p fwd : word),
  minv m -> getr R 17 = p ->
  wat m p V_FORWARD -> wat m (at_off p 8) fwd ->
  exists R2,
    msteps source_segs (mkst R (0x11c00 : word) m rom) (mkst R2 (0x11dae : word) m rom) /\
    getr R2 11 = fwd /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros m R p fwd I A17 H0 H1. pose proof I as [Hc _].
  eexists. split.
  - wld Hc SF_11c00 SD_11c00 p V_FORWARD ltac:(rewrite A17; apply v_addi_zero) H0.
    ws Hc SF_11c04 SD_11c04.
    wbr_ft Hc SF_11c08 SD_11c08 ltac:(vm_compute; reflexivity).
    wld Hc SF_11c0c SD_11c0c (at_off p 8) fwd ltac:(rewrite A17; reflexivity) H1.
    wj Hc SF_11c10 SD_11c10 (0x11dae : word).
    apply mst_refl.
  - gres. repeat split. kept_frame.
Qed.

(** The memory after copying one pair, in the machine's order. *)
Definition pair_write (m : word -> option byte) (q p w0 w1 moved : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m q (w8 w0)) (at_off q 8) (w8 w1))
    (at_off c 16) (w8 (at_off q 16))) p (w8 V_FORWARD)) (at_off p 8) (w8 moved).

Definition pair_moved (q : word) : word := v_or (Z_to_bv 64 3) q.

Lemma minv_pair_write : forall m q p w0 w1 moved,
  minv m ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  minv (pair_write m q p w0 w1 moved).
Proof.
  intros m q p w0 w1 moved I Hp1 Hp2 Hq1 Hq2. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  unfold pair_write.
  apply minv_heap; [apply minv_heap; [apply minv_next; apply minv_heap; [apply minv_heap; [exact I|]|]|]|].
  - right. lia.
  - right. rewrite u_at_off by lia. lia.
  - left. lia.
  - left. rewrite u_at_off by lia. lia.
Qed.

(** Pair path, from the forwarding test to the first tail test. *)
Lemma body_pair_copy : forall m R (p q w0 w1 : word),
  minv m -> getr R 10 = c -> getr R 17 = p -> getr R 14 = Z_to_bv 64 3 ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  wat m p w0 -> w0 <> V_FORWARD -> wat m (at_off p 8) w1 ->
  wat m (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  exists Rx,
    msteps source_segs (mkst R (0x11c00 : word) m rom)
      (mkst Rx (0x11d70 : word) (pair_write m q p w0 w1 (pair_moved q)) rom) /\
    getr Rx 10 = c /\ getr Rx 11 = pair_moved q /\ getr Rx 12 = Z_to_bv 64 (tag w1) /\
    getr Rx 16 = Z_to_bv 64 3 /\ getr Rx 9 = w1 /\ getr Rx 15 = at_off q 16 /\
    getr Rx 5 = q /\ getr Rx 13 = getr R 13 /\ getr Rx 8 = Z_to_bv 64 16 /\
    getr Rx 2 = getr R 2 /\ (forall x : reg, kept x -> getr Rx x = getr R x).
Proof.
  intros m R p q w0 w1 I A10 A17 A14 Hp1 Hp2 H0 Hne H1 Hnx Hq1 Hq2.
  pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  assert (Uq8 : bv_unsigned (at_off q 8) = (bv_unsigned q + 8)%Z) by (apply u_at_off; lia).
  assert (Up8 : bv_unsigned (at_off p 8) = (bv_unsigned p + 8)%Z) by (apply u_at_off; lia).
  assert (U16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  pose proof I as [Hc _].
  set (m1 := wbytes m q (w8 w0)).
  assert (I1 : minv m1) by (apply minv_heap; [exact I|right; lia]).
  assert (W1 : wat m1 (at_off p 8) w1)
    by (apply wat_other; [exact H1|rewrite Up8; unfold fromhi in *; lia|lia|rewrite Up8; lia]).
  set (m2 := wbytes m1 (at_off q 8) (w8 w1)).
  assert (I2 : minv m2) by (apply minv_heap; [exact I1|right; rewrite Uq8; lia]).
  set (m3 := wbytes m2 (at_off c 16) (w8 (at_off q 16))).
  assert (I3 : minv m3) by (apply minv_next; exact I2).
  set (m4 := wbytes m3 p (w8 V_FORWARD)).
  assert (I4 : minv m4) by (apply minv_heap; [exact I3|left; lia]).
  set (m5 := wbytes m4 (at_off p 8) (w8 (pair_moved q))).
  assert (I5 : minv m5) by (apply minv_heap; [exact I4|left; rewrite Up8; lia]).
  assert (W2 : wat m5 (at_off q 8) w1).
  { apply wat_other; [apply wat_other; [apply wat_other; [apply wat_hit; rewrite Uq8; lia
      |rewrite Uq8, U16; lia|rewrite U16; lia|rewrite Uq8; lia]
      |rewrite Uq8; unfold fromhi in *; lia|lia|rewrite Uq8; lia]
      |rewrite Uq8, Up8; unfold fromhi in *; lia|rewrite Up8; lia|rewrite Uq8; lia]. }
  assert (H16 : v_slli (v_addi (Z_to_bv 64 0) 2) 3 = Z_to_bv 64 16) by bveq.
  assert (Hat16 : v_add q (Z_to_bv 64 16) = at_off q 16).
  { unfold v_add, at_off. rewrite (u_Z2bv 16) by lia. reflexivity. }
  eexists. split.
  - wld Hc SF_11c00 SD_11c00 p w0 ltac:(rewrite A17; apply v_addi_zero) H0.
    ws Hc SF_11c04 SD_11c04.
    wbr_tk Hc SF_11c08 SD_11c08 ltac:(apply ne_true; apply word_ne; exact Hne).
    wld Hc SF_11c12 SD_11c12 (at_off c 16) q ltac:(rewrite A10; reflexivity) Hnx.
    wsd Hc SF_11c16 SD_11c16 q w0 ltac:(apply v_addi_zero)
      ltac:(apply heap_store_ok; [exact I|right; lia]).
    wld (proj1 I1) SF_11c1a SD_11c1a (at_off p 8) w1 ltac:(rewrite A17; reflexivity) W1.
    wsd (proj1 I1) SF_11c1e SD_11c1e (at_off q 8) w1 ltac:(reflexivity)
      ltac:(apply heap_store_ok; [exact I1|right; rewrite Uq8; lia]).
    ws (proj1 I2) SF_11c22 SD_11c22.
    ws (proj1 I2) SF_11c24 SD_11c24.
    wbr_tk (proj1 I2) SF_11c26 SD_11c26 ltac:(rewrite A14; vm_compute; reflexivity).
    wsv (proj1 I2) SF_11d48 SD_11d48 (Z_to_bv 64 16) ltac:(exact H16).
    wsv (proj1 I2) SF_11d4c SD_11d4c (at_off q 16) ltac:(exact Hat16).
    wsd (proj1 I2) SF_11d50 SD_11d50 (at_off c 16) (at_off q 16) ltac:(rewrite A10; reflexivity)
      ltac:(apply next_store_ok; exact I2).
    wsv (proj1 I3) SF_11d52 SD_11d52 (pair_moved q) ltac:(rewrite A14; reflexivity).
    ws (proj1 I3) SF_11d56 SD_11d56.
    wsd (proj1 I3) SF_11d5a SD_11d5a p V_FORWARD ltac:(rewrite A17; apply v_addi_zero)
      ltac:(apply heap_store_ok; [exact I3|left; lia]).
    wsd (proj1 I4) SF_11d5e SD_11d5e (at_off p 8) (pair_moved q) ltac:(rewrite A17; reflexivity)
      ltac:(apply heap_store_ok; [exact I4|left; rewrite Up8; lia]).
    wbr_ft (proj1 I5) SF_11d62 SD_11d62 ltac:(rewrite A14; vm_compute; reflexivity).
    wld (proj1 I5) SF_11d66 SD_11d66 (at_off q 8) w1 ltac:(reflexivity) W2.
    wsv (proj1 I5) SF_11d6a SD_11d6a (Z_to_bv 64 (tag w1)) ltac:(apply andi7).
    ws (proj1 I5) SF_11d6e SD_11d6e.
    unfold pair_write. apply mst_refl.
  - gres. repeat split; try assumption; try bveq.
    kept_frame.
Qed.

(** A pair whose tail isn't a pair: the loop never runs. *)
Lemma body_pair_leaf : forall m R (p q w0 w1 : word),
  minv m -> getr R 10 = c -> getr R 17 = p -> getr R 14 = Z_to_bv 64 3 ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  wat m p w0 -> w0 <> V_FORWARD -> wat m (at_off p 8) w1 ->
  wat m (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  tag w1 <> 3%Z ->
  exists R2,
    msteps source_segs (mkst R (0x11c00 : word) m rom)
      (mkst R2 (0x11dae : word) (pair_write m q p w0 w1 (pair_moved q)) rom) /\
    getr R2 11 = pair_moved q /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros m R p q w0 w1 I A10 A17 A14 Hp1 Hp2 H0 Hne H1 Hnx Hq1 Hq2 Ht.
  destruct (body_pair_copy m R p q w0 w1 I A10 A17 A14 Hp1 Hp2 H0 Hne H1 Hnx Hq1 Hq2)
    as (Rx & Hm & B10 & B11 & B12 & B16 & B9 & B15 & B5 & B13 & B8 & B2 & Bk).
  pose proof (minv_pair_write m q p w0 w1 (pair_moved q) I Hp1 Hp2 Hq1 Hq2) as I2.
  exists Rx. split; [|split; [exact B11|split; assumption]].
  eapply msteps_trans; [exact Hm|].
  wbr_tk (proj1 I2) SF_11d70 SD_11d70 ltac:(rewrite B12, B16; apply ne_true;
    pose proof (tag_range w1); rewrite !u_Z2bv by lia; exact Ht).
  apply mst_refl.
Qed.

(** A pair whose tail is a pair: the loop runs per the [spine] relation. *)
Lemma body_pair_spine : forall m R (p q w0 w1 : word) m' cur',
  minv m -> getr R 10 = c -> getr R 17 = p -> getr R 14 = Z_to_bv 64 3 -> getr R 13 = from ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  wat m p w0 -> w0 <> V_FORWARD -> wat m (at_off p 8) w1 ->
  wat m (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  tag w1 = 3%Z ->
  spine (pair_write m q p w0 w1 (pair_moved q)) (at_off q 16) w1 m' cur' ->
  exists R2,
    msteps source_segs (mkst R (0x11c00 : word) m rom) (mkst R2 (0x11dae : word) m' rom) /\
    getr R2 11 = pair_moved q /\ getr R2 2 = getr R 2 /\ minv m' /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros m R p q w0 w1 m' cur' I A10 A17 A14 A13 Hp1 Hp2 H0 Hne H1 Hnx Hq1 Hq2 Ht Hs.
  destruct (body_pair_copy m R p q w0 w1 I A10 A17 A14 Hp1 Hp2 H0 Hne H1 Hnx Hq1 Hq2)
    as (Rx & Hm & B10 & B11 & B12 & B16 & B9 & B15 & B5 & B13 & B8 & B2 & Bk).
  pose proof (minv_pair_write m q p w0 w1 (pair_moved q) I Hp1 Hp2 Hq1 Hq2) as I2.
  set (M := pair_write m q p w0 w1 (pair_moved q)) in *.
  assert (Hat : v_add (Z_to_bv 64 16) q = at_off q 16).
  { unfold v_add, at_off. rewrite (u_Z2bv 16) by lia. f_equal. lia. }
  assert (Hmid : exists Ry,
     msteps source_segs (mkst Rx (0x11d70 : word) M rom) (mkst Ry (0x11d7a : word) M rom) /\
     spine_regs Ry (at_off q 16) w1 /\ getr Ry 11 = pair_moved q /\ getr Ry 2 = getr R 2 /\
     (forall x : reg, kept x -> getr Ry x = getr R x)).
  { eexists. split.
    - wbr_ft (proj1 I2) SF_11d70 SD_11d70 ltac:(rewrite B12, B16, Ht; apply ne_false; reflexivity).
      wsv (proj1 I2) SF_11d74 SD_11d74 (at_off q 16) ltac:(rewrite B8, B5; exact Hat).
      ws (proj1 I2) SF_11d76 SD_11d76.
      apply mst_refl.
    - unfold spine_regs. gres. repeat split; try assumption; try reflexivity; try (rewrite B13; assumption).
      intros x Hx. pose proof Hx as Hy. unfold kept in Hy. decompose [and] Hy.
      rewrite !getr_other by assumption. apply Bk; exact Hx. }
  destruct Hmid as (Ry & Hm1 & Hr & C11 & C2 & Ck).
  destruct (spine_loop M (at_off q 16) w1 m' cur' Hs Ry I2 Hr) as (Rf & Hm2 & [D10 [D11 [D2 Dk]]] & I3).
  exists Rf. split.
  - eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm1|exact Hm2].
  - rewrite D11, D2. split; [exact C11|split; [exact C2|split; [exact I3|]]].
    intros x Hx. rewrite Dk, Ck by exact Hx. reflexivity.
Qed.

(** ** Objects other than pairs: copy [n] words, then forward. *)

Fixpoint copy_from (m : word -> option byte) (q : word) (src : Z -> word) (i : Z) (k : nat) :=
  match k with
  | O => m
  | S k' => copy_from (wbytes m (at_off q (8 * i)) (w8 (src i))) q src (i + 1) k'
  end.

Lemma at_off_step : forall (x : word) (k : Z), (0 <= bv_unsigned x + k < 2^64)%Z ->
  v_addi (at_off x k) 8 = at_off x (k + 8).
Proof.
  intros x k H. unfold v_addi. rewrite u_at_off by exact H. unfold at_off. f_equal. lia.
Qed.

Lemma at_off_0 : forall x : word, at_off x 0 = x.
Proof.
  intros x. apply bv_eq. unfold at_off. rewrite Z.add_0_r. rewrite Z_to_bv_unsigned.
  apply bv_wrap_bv_unsigned.
Qed.

Definition obj_loop_post (R R2 : bvmap 5 word) : Prop :=
  getr R2 10 = getr R 10 /\ getr R2 5 = getr R 5 /\ getr R2 17 = getr R 17 /\
  getr R2 14 = getr R 14 /\ getr R2 16 = getr R 16 /\ getr R2 11 = getr R 11 /\
  getr R2 2 = getr R 2 /\ (forall x : reg, kept x -> getr R2 x = getr R x).

(** The word-copy loop at 0x11d3a. *)
Lemma obj_loop : forall (k : nat) i m R (q p : word) (src : Z -> word) (n : Z),
  minv m -> (2 <= i)%Z -> (i + Z.of_nat (S k) = n)%Z ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 8 * n <= bv_unsigned tohi)%Z ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 8 * n <= fromhi)%Z ->
  (forall j, (0 <= j < n)%Z -> wat m (at_off p (8 * j)) (src j)) ->
  getr R 15 = at_off q (8 * i) -> getr R 12 = at_off p (8 * i) -> getr R 9 = at_off q (8 * n) ->
  exists R2,
    msteps source_segs (mkst R (0x11d3a : word) m rom)
      (mkst R2 (0x11d46 : word) (copy_from m q src i (S k)) rom) /\
    obj_loop_post R R2 /\ minv (copy_from m q src i (S k)).
Proof.
  pose proof ranges as (R0 & R1 & R2 & R3).
  induction k as [|k IH]; intros i m R q p src n I Hi Hn Hq1 Hq2 Hp1 Hp2 Hs A15 A12 A9.
  all: pose proof (bv_unsigned_in_range _ q) as Rc; pose proof (bv_unsigned_in_range _ p) as Rp;
    change (bv_modulus 64) with (2^64)%Z in Rc, Rp;
    pose proof I as [Hc _];
    assert (Hin : in_heap (bv_unsigned (at_off q (8 * i))))
      by (right; rewrite u_at_off by lia; rewrite Nat2Z.inj_succ in Hn; lia);
    pose proof (Hs i ltac:(rewrite Nat2Z.inj_succ in Hn; lia)) as Hw;
    pose proof (minv_heap m (at_off q (8 * i)) (src i) I Hin) as I1;
    rewrite Nat2Z.inj_succ in Hn;
    assert (Hq8 : v_addi (at_off q (8 * i)) 8 = at_off q (8 * (i + 1)))
      by (rewrite at_off_step by lia; f_equal; lia);
    assert (Hp8 : v_addi (at_off p (8 * i)) 8 = at_off p (8 * (i + 1)))
      by (rewrite at_off_step by lia; f_equal; lia).
  - assert (En : (n = i + 1)%Z) by lia.
    eexists. split; [|split; [|exact I1]].
    + wld Hc SF_11d3a SD_11d3a (at_off p (8 * i)) (src i) ltac:(rewrite A12; apply v_addi_zero) Hw.
      wsd Hc SF_11d3c SD_11d3c (at_off q (8 * i)) (src i) ltac:(rewrite A15; apply v_addi_zero)
        ltac:(apply heap_store_ok; assumption).
      wsv (proj1 I1) SF_11d3e SD_11d3e (at_off q (8 * (i + 1))) ltac:(rewrite A15; exact Hq8).
      wsv (proj1 I1) SF_11d40 SD_11d40 (at_off p (8 * (i + 1))) ltac:(rewrite A12; exact Hp8).
      wbr_ft (proj1 I1) SF_11d42 SD_11d42 ltac:(rewrite A9; apply ne_false; rewrite En; reflexivity).
      apply mst_refl.
    + unfold obj_loop_post. gres. repeat split. kept_frame.
  - set (m1 := wbytes m (at_off q (8 * i)) (w8 (src i))) in *.
    assert (Hb : exists Rx,
       msteps source_segs (mkst R (0x11d3a : word) m rom) (mkst Rx (0x11d3a : word) m1 rom) /\
       getr Rx 15 = at_off q (8 * (i + 1)) /\ getr Rx 12 = at_off p (8 * (i + 1)) /\
       getr Rx 9 = at_off q (8 * n) /\ obj_loop_post R Rx).
    { eexists. split.
      - wld Hc SF_11d3a SD_11d3a (at_off p (8 * i)) (src i) ltac:(rewrite A12; apply v_addi_zero) Hw.
        wsd Hc SF_11d3c SD_11d3c (at_off q (8 * i)) (src i) ltac:(rewrite A15; apply v_addi_zero)
          ltac:(apply heap_store_ok; assumption).
        wsv (proj1 I1) SF_11d3e SD_11d3e (at_off q (8 * (i + 1))) ltac:(rewrite A15; exact Hq8).
        wsv (proj1 I1) SF_11d40 SD_11d40 (at_off p (8 * (i + 1))) ltac:(rewrite A12; exact Hp8).
        wbr_tk (proj1 I1) SF_11d42 SD_11d42 ltac:(rewrite A9; apply ne_true;
          rewrite !u_at_off by (rewrite Nat2Z.inj_succ in Hn; lia);
          rewrite Nat2Z.inj_succ in Hn; lia).
        apply mst_refl.
      - gres. split; [reflexivity|]. split; [reflexivity|]. split; [exact A9|].
        unfold obj_loop_post. gres. repeat split. kept_frame. }
    destruct Hb as (Rx & Hm & B15 & B12 & B9 & [P10 [P5 [P17 [P14 [P16 [P11 [P2 Pk]]]]]]]).
    assert (Hs1 : forall j, (0 <= j < n)%Z -> wat m1 (at_off p (8 * j)) (src j)).
    { intros j Hj. apply wat_other; [apply Hs; exact Hj| |rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia].
      rewrite !u_at_off by lia. unfold fromhi in *. lia. }
    destruct (IH (i + 1)%Z m1 Rx q p src n I1 ltac:(lia) ltac:(rewrite Nat2Z.inj_succ; lia)
                 Hq1 Hq2 Hp1 Hp2 Hs1 B15 B12 B9) as (Rf & Hm2 & [Q10 [Q5 [Q17 [Q14 [Q16 [Q11 [Q2 Qk]]]]]]] & I2).
    exists Rf. split; [eapply msteps_trans; [exact Hm|exact Hm2]|]. split; [|exact I2].
    unfold obj_loop_post. rewrite Q10, Q5, Q17, Q14, Q16, Q11, Q2.
    do 7 (split; [assumption|]). intros x Hx. rewrite Qk, Pk by exact Hx. reflexivity.
Qed.

Lemma minv_copy_from : forall k i m (q : word) src n,
  minv m -> (2 <= i)%Z -> (i + Z.of_nat k = n)%Z ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 8 * n <= bv_unsigned tohi)%Z ->
  minv (copy_from m q src i k).
Proof.
  pose proof ranges as (R0 & R1 & R2 & R3).
  induction k as [|k IH]; intros i m q src n I Hi Hn Hq1 Hq2; [exact I|].
  pose proof (bv_unsigned_in_range _ q) as Rc. change (bv_modulus 64) with (2^64)%Z in Rc.
  rewrite Nat2Z.inj_succ in Hn. cbn [copy_from].
  apply (IH (i + 1)%Z _ q src n); try lia.
  apply minv_heap; [exact I|]. right. rewrite u_at_off by lia. lia.
Qed.

(** After the copy: every word below [i] is unchanged, and each word from [i] holds [src]. *)
Lemma copy_from_keeps : forall k i m (q a x : word) src,
  wat m a x ->
  (forall j, (i <= j < i + Z.of_nat k)%Z ->
     (bv_unsigned (at_off q (8 * j)) + 8 <= bv_unsigned a \/
      bv_unsigned a + 8 <= bv_unsigned (at_off q (8 * j)))%Z /\
     (bv_unsigned (at_off q (8 * j)) + 8 <= 2^64)%Z) ->
  (bv_unsigned a + 8 <= 2^64)%Z ->
  wat (copy_from m q src i k) a x.
Proof.
  induction k as [|k IH]; intros i m q a x src Hw Hd Ha; [exact Hw|].
  cbn [copy_from]. apply IH; [| |exact Ha].
  - destruct (Hd i ltac:(rewrite Nat2Z.inj_succ; lia)) as [D1 D2].
    apply wat_other; [exact Hw|lia|exact D2|exact Ha].
  - intros j Hj. apply Hd. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma copy_from_wrote : forall k i m (q : word) src j,
  (i <= j < i + Z.of_nat k)%Z -> (0 <= i)%Z ->
  (bv_unsigned q + 8 * (i + Z.of_nat k) <= 2^64)%Z ->
  wat (copy_from m q src i k) (at_off q (8 * j)) (src j).
Proof.
  induction k as [|k IH]; intros i m q src j Hj Hi Hb; [lia|].
  pose proof (bv_unsigned_in_range _ q) as Rc. change (bv_modulus 64) with (2^64)%Z in Rc.
  rewrite Nat2Z.inj_succ in Hj, Hb. cbn [copy_from].
  destruct (Z.eq_dec j i) as [->|Hne].
  - apply copy_from_keeps.
    + apply wat_hit. rewrite u_at_off by lia. lia.
    + intros j Hj2. rewrite !u_at_off by lia. split; lia.
    + rewrite u_at_off by lia. lia.
  - apply IH; lia.
Qed.

Definition obj_moved (t : Z) (q : word) : word := v_or (Z_to_bv 64 t) q.

Definition obj_write (m : word -> option byte) (q p : word) (src : Z -> word) (n t : Z) :=
  wbytes (wbytes (wbytes
    (copy_from (wbytes (wbytes m q (w8 (src 0%Z))) (at_off q 8) (w8 (src 1%Z))) q src 2 (Z.to_nat (n - 2)))
    (at_off c 16) (w8 (at_off q (8 * n))))
    p (w8 V_FORWARD)) (at_off p 8) (w8 (obj_moved t q)).

(** The final writes, from 0x11d48 to the exit. *)
Lemma obj_tail : forall m R (p q : word) (n t : Z),
  minv m -> getr R 10 = c -> getr R 5 = q -> getr R 17 = p ->
  getr R 15 = Z_to_bv 64 n -> getr R 14 = Z_to_bv 64 t -> getr R 16 = Z_to_bv 64 3 ->
  (0 <= t < 8)%Z -> t <> 3%Z -> (0 <= n)%Z ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  (bv_unsigned q + 8 * n <= bv_unsigned tohi)%Z -> (bv_unsigned q0 <= bv_unsigned q)%Z ->
  exists R2,
    msteps source_segs (mkst R (0x11d48 : word) m rom)
      (mkst R2 (0x11dae : word)
         (wbytes (wbytes (wbytes m (at_off c 16) (w8 (at_off q (8 * n))))
            p (w8 V_FORWARD)) (at_off p 8) (w8 (obj_moved t q))) rom) /\
    getr R2 11 = obj_moved t q /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros m R p q n t I A10 A5 A17 A15 A14 A16 Ht Ht3 Hn Hp1 Hp2 Hq2 Hq1.
  pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  assert (Up8 : bv_unsigned (at_off p 8) = (bv_unsigned p + 8)%Z) by (apply u_at_off; lia).
  assert (Hat : v_add q (v_slli (Z_to_bv 64 n) 3) = at_off q (8 * n)).
  { unfold v_add, v_slli, at_off. rewrite (u_Z2bv n) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    change (2^3)%Z with 8%Z. rewrite u_Z2bv by lia. f_equal. lia. }
  pose proof I as [Hc _].
  pose proof (minv_next m (at_off q (8 * n)) I) as I1.
  set (m1 := wbytes m (at_off c 16) (w8 (at_off q (8 * n)))) in *.
  assert (I2 : minv (wbytes m1 p (w8 V_FORWARD))) by (apply minv_heap; [exact I1|left; lia]).
  eexists. split.
  - ws Hc SF_11d48 SD_11d48.
    wsv Hc SF_11d4c SD_11d4c (at_off q (8 * n)) ltac:(rewrite A5, A15; exact Hat).
    wsd Hc SF_11d50 SD_11d50 (at_off c 16) (at_off q (8 * n)) ltac:(rewrite A10; reflexivity)
      ltac:(apply next_store_ok; exact I).
    wsv (proj1 I1) SF_11d52 SD_11d52 (obj_moved t q) ltac:(rewrite A14, A5; reflexivity).
    ws (proj1 I1) SF_11d56 SD_11d56.
    wsd (proj1 I1) SF_11d5a SD_11d5a p V_FORWARD ltac:(rewrite A17; apply v_addi_zero)
      ltac:(apply heap_store_ok; [exact I1|left; lia]).
    wsd (proj1 I2) SF_11d5e SD_11d5e (at_off p 8) (obj_moved t q) ltac:(rewrite A17; reflexivity)
      ltac:(apply heap_store_ok; [exact I2|left; rewrite Up8; lia]).
    wbr_tk (proj1 (minv_heap _ (at_off p 8) (obj_moved t q) I2 ltac:(left; rewrite Up8; lia)))
      SF_11d62 SD_11d62 ltac:(rewrite A14, A16; apply ne_true; rewrite !u_Z2bv by lia; exact Ht3).
    apply mst_refl.
  - gres. repeat split. kept_frame.
Qed.

Lemma obj_words_ge2 : forall h : word, (1 <= hdr_type (bv_unsigned h) <= 11)%Z ->
  (2 <= obj_words_Z (bv_unsigned h))%Z.
Proof.
  intros h Ht. pose proof (hdr_size_range h) as Hs.
  assert (Hd : (0 <= (hdr_size (bv_unsigned h) + 7) / 8)%Z) by (apply Z.div_pos; lia).
  assert (Ha : forall w, (2 <= at_least_two w)%Z).
  { intros w. unfold at_least_two. destruct (Z.ltb_spec w 2); lia. }
  unfold obj_words_Z. cbv zeta.
  remember (hdr_type (bv_unsigned h)) as t eqn:Et.
  assert (Hc : (t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/
                t = 9 \/ t = 10 \/ t = 11)%Z) by lia.
  destruct Hc as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; simpl; try lia; apply Ha.
Qed.

(** THEOREM (body): copying any object that isn't a pair. *)
Theorem body_object : forall m R (p q h : word) (src : Z -> word) t,
  minv m -> getr R 10 = c -> getr R 17 = p -> getr R 14 = Z_to_bv 64 t ->
  (t = 1 \/ t = 5 \/ t = 6)%Z ->
  (forall j, (0 <= j < obj_words_Z (bv_unsigned h))%Z -> wat m (at_off p (8 * j)) (src j)) ->
  src 0%Z = h -> h <> V_FORWARD ->
  (1 <= hdr_type (bv_unsigned h) <= 11)%Z ->
  (bv_unsigned from <= bv_unsigned p)%Z ->
  (bv_unsigned p + 8 * obj_words_Z (bv_unsigned h) <= fromhi)%Z ->
  wat m (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z ->
  (bv_unsigned q + 8 * obj_words_Z (bv_unsigned h) <= bv_unsigned tohi)%Z ->
  exists R2,
    msteps source_segs (mkst R (0x11c00 : word) m rom)
      (mkst R2 (0x11dae : word) (obj_write m q p src (obj_words_Z (bv_unsigned h)) t) rom) /\
    getr R2 11 = obj_moved t q /\ getr R2 2 = getr R 2 /\
    (forall x : reg, kept x -> getr R2 x = getr R x).
Proof.
  intros m R p q h src t I A10 A17 A14 Ht Hs E0 Hne Hty Hp1 Hp2 Hnx Hq1 Hq2.
  pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (obj_words_ge2 h Hty) as Hn2.
  set (n := obj_words_Z (bv_unsigned h)) in *.
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  assert (Uq8 : bv_unsigned (at_off q 8) = (bv_unsigned q + 8)%Z) by (apply u_at_off; lia).
  assert (Up8 : bv_unsigned (at_off p 8) = (bv_unsigned p + 8)%Z) by (apply u_at_off; lia).
  assert (Ht3 : t <> 3%Z) by lia. assert (Ht8 : (0 <= t < 8)%Z) by lia.
  pose proof (Hs 0%Z ltac:(lia)) as H0. change (8 * 0)%Z with 0%Z in H0. rewrite at_off_0 in H0.
  pose proof (Hs 1%Z ltac:(lia)) as H1. change (8 * 1)%Z with 8%Z in H1.
  rewrite E0 in H0.
  pose proof I as [Hc _].
  set (m1 := wbytes m q (w8 h)).
  assert (I1 : minv m1) by (apply minv_heap; [exact I|right; lia]).
  assert (W1 : wat m1 (at_off p 8) (src 1%Z))
    by (apply wat_other; [exact H1|rewrite Up8; unfold fromhi in *; lia|lia|rewrite Up8; lia]).
  set (m2 := wbytes m1 (at_off q 8) (w8 (src 1%Z))).
  assert (I2 : minv m2) by (apply minv_heap; [exact I1|right; rewrite Uq8; lia]).
  assert (Hdisj : forall j, (0 <= j < n)%Z -> forall x : word,
     (bv_unsigned q0 <= bv_unsigned x)%Z -> (bv_unsigned x + 8 <= bv_unsigned tohi)%Z ->
     (bv_unsigned x + 8 <= bv_unsigned (at_off p (8 * j)) \/
      bv_unsigned (at_off p (8 * j)) + 8 <= bv_unsigned x)%Z).
  { intros j Hj x X1 X2. rewrite u_at_off by lia. unfold fromhi in *. lia. }
  assert (Hs2 : forall j, (0 <= j < n)%Z -> wat m2 (at_off p (8 * j)) (src j)).
  { intros j Hj.
    pose proof (Hdisj j Hj q ltac:(lia) ltac:(lia)) as D1.
    pose proof (Hdisj j Hj (at_off q 8) ltac:(lia) ltac:(lia)) as D2.
    rewrite Uq8 in D2.
    apply wat_other; [apply wat_other; [apply Hs; exact Hj|lia|lia|rewrite u_at_off by lia; lia]
      |rewrite Uq8; lia|lia|rewrite u_at_off by lia; lia]. }
  assert (W0 : wat m2 p h).
  { pose proof (Hs2 0%Z ltac:(lia)) as W. change (8 * 0)%Z with 0%Z in W.
    rewrite at_off_0, E0 in W. exact W. }
  assert (Hpre : exists Rx,
     msteps source_segs (mkst R (0x11c00 : word) m rom) (mkst Rx (0x11c2a : word) m2 rom) /\
     getr Rx 10 = c /\ getr Rx 5 = q /\ getr Rx 17 = p /\ getr Rx 14 = Z_to_bv 64 t /\
     getr Rx 16 = Z_to_bv 64 3 /\ getr Rx 15 = Z_to_bv 64 2 /\ getr Rx 2 = getr R 2 /\
     (forall x : reg, kept x -> getr Rx x = getr R x)).
  { eexists. split.
    - wld Hc SF_11c00 SD_11c00 p h ltac:(rewrite A17; apply v_addi_zero) H0.
      ws Hc SF_11c04 SD_11c04.
      wbr_tk Hc SF_11c08 SD_11c08 ltac:(apply ne_true; apply word_ne; exact Hne).
      wld Hc SF_11c12 SD_11c12 (at_off c 16) q ltac:(rewrite A10; reflexivity) Hnx.
      wsd Hc SF_11c16 SD_11c16 q h ltac:(apply v_addi_zero)
        ltac:(apply heap_store_ok; [exact I|right; lia]).
      wld (proj1 I1) SF_11c1a SD_11c1a (at_off p 8) (src 1%Z) ltac:(rewrite A17; reflexivity) W1.
      wsd (proj1 I1) SF_11c1e SD_11c1e (at_off q 8) (src 1%Z) ltac:(reflexivity)
        ltac:(apply heap_store_ok; [exact I1|right; rewrite Uq8; lia]).
      ws (proj1 I2) SF_11c22 SD_11c22.
      ws (proj1 I2) SF_11c24 SD_11c24.
      wbr_ft (proj1 I2) SF_11c26 SD_11c26 ltac:(rewrite A14; apply eq_false;
        assert (U3 : bv_unsigned (v_addi (Z_to_bv 64 0) 3) = 3%Z) by (vm_compute; reflexivity);
        rewrite U3, u_Z2bv by lia; exact Ht3).
      apply mst_refl.
    - gres. repeat split; try assumption; try bveq. kept_frame. }
  destruct Hpre as (Rx & Hm & B10 & B5 & B17 & B14 & B16 & B15 & B2 & Bk).
  destruct (obj_size Rx m2 rom p h (proj1 I2) B17 W0 B15 Hty)
    as [[En (Ry & Hm2 & C15 & [C10 [C5 [C17 [C14 [C16 [C2 Ck]]]]]])]
       |[Hge (Ry & Hm2 & C11 & [C10 [C5 [C17 [C14 [C16 [C2 Ck]]]]]])]].
  - (* two words: no loop *)
    fold n in En.
    destruct (obj_tail m2 Ry p q n t I2 ltac:(rewrite C10; exact B10) ltac:(rewrite C5; exact B5)
                ltac:(rewrite C17; exact B17) ltac:(rewrite En; exact C15)
                ltac:(rewrite C14; exact B14) ltac:(rewrite C16; exact B16)
                Ht8 Ht3 ltac:(lia) Hp1 ltac:(lia) Hq2 Hq1)
      as (Rf & Hm3 & D11 & D2 & Dk).
    exists Rf. split.
    + eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm2|].
      assert (Ez : Z.to_nat (n - 2) = 0%nat) by (rewrite En; reflexivity).
      unfold obj_write. rewrite Ez, E0. cbn [copy_from]. exact Hm3.
    + split; [exact D11|]. split; [rewrite D2, C2; exact B2|].
      intros x Hx. rewrite Dk, Ck, Bk by exact Hx. reflexivity.
  - (* three or more: the copy loop *)
    fold n in Hge, C11.
    assert (Hat16 : forall x : word, (0 <= bv_unsigned x + 16 < 2^64)%Z -> v_addi x 16 = at_off x (8 * 2)).
    { intros x Hx. reflexivity. }
    assert (Hend : v_add (v_slli (Z_to_bv 64 n) 3) q = at_off q (8 * n)).
    { unfold v_add, v_slli, at_off. rewrite (u_Z2bv n) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      change (2^3)%Z with 8%Z. rewrite u_Z2bv by lia. f_equal. lia. }
    assert (Hmid : exists Rz,
       msteps source_segs (mkst Ry (0x11d2c : word) m2 rom) (mkst Rz (0x11d3a : word) m2 rom) /\
       getr Rz 15 = at_off q (8 * 2) /\ getr Rz 12 = at_off p (8 * 2) /\ getr Rz 9 = at_off q (8 * n) /\
       getr Rz 10 = c /\ getr Rz 5 = q /\ getr Rz 17 = p /\ getr Rz 14 = Z_to_bv 64 t /\
       getr Rz 16 = Z_to_bv 64 3 /\ getr Rz 11 = Z_to_bv 64 n /\ getr Rz 2 = getr Ry 2 /\
       (forall x : reg, kept x -> getr Rz x = getr Ry x)).
    { eexists. split.
      - wsv (proj1 I2) SF_11d2c SD_11d2c (at_off q (8 * 2)) ltac:(rewrite C5, B5; reflexivity).
        wsv (proj1 I2) SF_11d30 SD_11d30 (at_off p (8 * 2)) ltac:(rewrite C17, B17; reflexivity).
        ws (proj1 I2) SF_11d34 SD_11d34.
        wsv (proj1 I2) SF_11d38 SD_11d38 (at_off q (8 * n)) ltac:(rewrite C11, C5, B5; exact Hend).
        apply mst_refl.
      - gres. repeat split; try reflexivity; try (rewrite ?C10, ?C5, ?C17, ?C14, ?C16; assumption).
        kept_frame. }
    destruct Hmid as (Rz & Hm3 & E15 & E12 & E9 & E10 & E5 & E17 & E14 & E16 & E11 & E2 & Ek).
    set (k := Z.to_nat (n - 3)).
    assert (Hkn : Z.to_nat (n - 2) = S k).
    { unfold k. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
    destruct (obj_loop k 2%Z m2 Rz q p src n I2 ltac:(lia)
                ltac:(unfold k; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia)
                Hq1 Hq2 Hp1 Hp2 Hs2 E15 E12 E9)
      as (Rl & Hm4 & [F10 [F5 [F17 [F14 [F16 [F11 [F2 Fk]]]]]]] & I3).
    set (m3 := copy_from m2 q src 2 (S k)) in *.
    assert (Hmv : exists Rv,
       msteps source_segs (mkst Rl (0x11d46 : word) m3 rom) (mkst Rv (0x11d48 : word) m3 rom) /\
       getr Rv 15 = Z_to_bv 64 n /\ getr Rv 10 = c /\ getr Rv 5 = q /\ getr Rv 17 = p /\
       getr Rv 14 = Z_to_bv 64 t /\ getr Rv 16 = Z_to_bv 64 3 /\ getr Rv 2 = getr Rl 2 /\
       (forall x : reg, kept x -> getr Rv x = getr Rl x)).
    { eexists. split.
      - wsv (proj1 I3) SF_11d46 SD_11d46 (Z_to_bv 64 n) ltac:(rewrite F11, E11; apply v_add_zero_l).
        apply mst_refl.
      - gres. repeat split; try (rewrite ?F10, ?F5, ?F17, ?F14, ?F16; assumption). kept_frame. }
    destruct Hmv as (Rv & Hm5 & G15 & G10 & G5 & G17 & G14 & G16 & G2 & Gk).
    destruct (obj_tail m3 Rv p q n t I3 G10 G5 G17 G15 G14 G16 Ht8 Ht3 ltac:(lia) Hp1 ltac:(lia) Hq2 Hq1)
      as (Rf & Hm6 & D11 & D2 & Dk).
    exists Rf. split.
    + eapply msteps_trans; [exact Hm|]. eapply msteps_trans; [exact Hm2|].
      eapply msteps_trans; [exact Hm3|]. eapply msteps_trans; [exact Hm4|].
      eapply msteps_trans; [exact Hm5|].
      unfold obj_write. rewrite Hkn, E0. exact Hm6.
    + split; [exact D11|]. split.
      * rewrite D2, G2, F2, E2, C2. exact B2.
      * intros x Hx. rewrite Dk, Gk, Fk, Ek, Ck, Bk by exact Hx. reflexivity.
Qed.

(** ** The whole function: entry, dispatch, a path, and exit. *)

(** What a caller of [copy_value] must establish. *)
Definition cv_pre (regs : bvmap 5 word) mem (sp v : word) : Prop :=
  mem_clear mem TL TH /\ getr regs 2 = sp /\ fp = at_off sp (-48) /\ stack_ok sp /\
  writable mem (bv_unsigned sp - 48) (bv_unsigned sp) /\
  getr regs 1 = ra /\ getr regs 8 = s0 /\ getr regs 9 = s1 /\ getr regs 18 = s2 /\ getr regs 19 = s3 /\
  (bv_unsigned ra mod 2 = 0)%Z /\
  getr regs 10 = c /\ getr regs 11 = v /\
  writable mem (bv_unsigned from) fromhi /\ writable mem (bv_unsigned q0) (bv_unsigned tohi) /\
  writable mem (bv_unsigned c) (bv_unsigned c + 24) /\
  wat mem c from /\ wat mem (at_off c 8) fw.

Definition M (mem : word -> option byte) := push_mem mem fp ra s0 s1 s2 s3.

Lemma heap_keep : forall mem (a x : word),
  wat mem a x ->
  (bv_unsigned a + 8 <= bv_unsigned fp + 8 \/ bv_unsigned fp + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= 2^64)%Z ->
  wat (M mem) a x.
Proof.
  intros mem a x Hw Hd Ha. pose proof ranges as (R0 & R1 & _). unfold M.
  apply wat_push; [exact Hw|lia|exact Hd|exact Ha].
Qed.

Lemma minv_M : forall regs mem sp v, cv_pre regs mem sp v -> minv (M mem).
Proof.
  intros regs mem sp v (Hc & A2 & Efp & Hst & Hw & A1 & A8 & A9 & A18 & A19 & Hev & A10 & A11 & W1 & W2 & W3 & Hf & Hfw).
  pose proof ranges as (R0 & R1 & R2 & R3).
  assert (Hfu : (TH <= bv_unsigned fp)%Z) by lia.
  assert (Hg : mem_grows mem (M mem)).
  { unfold M. apply push_grows. }
  unfold minv. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold M. apply push_clear; [exact Hc|exact Hfu|lia].
  - eapply writable_grows; [exact Hg|exact W1].
  - eapply writable_grows; [exact Hg|exact W2].
  - eapply writable_grows; [exact Hg|exact W3].
  - apply heap_keep; [exact Hf|lia|lia].
  - apply heap_keep; [exact Hfw|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia].
  - unfold M. apply push_framed. lia.
Qed.

(** Run the function given a path from the forwarding test to the exit. *)
Lemma top_compose : forall regs mem sp v m2 Rf Rt res,
  cv_pre regs mem sp v ->
  msteps source_segs (mkst (regupd regs 2 fp) (0x11bcc : word) (M mem) rom) (mkst Rt (0x11c00 : word) (M mem) rom) ->
  getr Rt 2 = getr (regupd regs 2 fp) 2 ->
  (forall x : reg, kept x -> getr Rt x = getr (regupd regs 2 fp) x) ->
  msteps source_segs (mkst Rt (0x11c00 : word) (M mem) rom) (mkst Rf (0x11dae : word) m2 rom) ->
  getr Rf 11 = res -> getr Rf 2 = getr Rt 2 ->
  (forall x : reg, kept x -> getr Rf x = getr Rt x) ->
  minv m2 ->
  returns regs rom mem m2 res.
Proof.
  intros regs mem sp v m2 Rf Rt res Hpre Hm1 T2 Tk Hm2 F11 F2 Fk Im2.
  pose proof Hpre as (Hc & A2 & Efp & Hst & Hw & A1 & A8 & A9 & A18 & A19 & Hev & _).
  pose proof Im2 as [Hc2 [_ [_ [_ [_ [_ Hfr]]]]]].
  unfold M in Hm1, Hm2.
  rewrite Efp in Hm1, Hm2, T2, Tk, Hfr.
  eapply (cv_compose regs mem rom sp res m2 Rf Hc A2 Hst Hw); cbv zeta.
  - rewrite A1. exact Hev.
  - rewrite A1, A8, A9, A18, A19.
    eapply msteps_trans; [exact Hm1|exact Hm2].
  - exact F11.
  - rewrite F2, T2. apply getr_same. reg_neq_tac.
  - intros x Hx. rewrite Fk, Tk by exact Hx. reflexivity.
  - exact Hc2.
  - rewrite A1, A8, A9, A18, A19. exact Hfr.
Qed.

(** The path from the tag test to the forwarding test, on the pushed memory. *)
Lemma top_test : forall regs mem sp v,
  cv_pre regs mem sp v -> is_ptr_tag (tag v) -> in_from from fw (ptr_of v) ->
  exists Rt,
    msteps source_segs (mkst (regupd regs 2 fp) (0x11bcc : word) (M mem) rom)
      (mkst Rt (0x11c00 : word) (M mem) rom) /\
    getr Rt 10 = c /\ getr Rt 11 = v /\ getr Rt 14 = Z_to_bv 64 (tag v) /\
    getr Rt 13 = from /\ getr Rt 17 = ptr_of v /\
    getr Rt 2 = getr (regupd regs 2 fp) 2 /\
    (forall x : reg, kept x -> getr Rt x = getr (regupd regs 2 fp) x).
Proof.
  intros regs mem sp v Hpre Ht Hif.
  pose proof (minv_M regs mem sp v Hpre) as I.
  pose proof I as [Hc [_ [_ [_ [Hf [Hfw _]]]]]].
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A10 & A11 & _).
  eapply (cv_to_test (regupd regs 2 fp) (M mem) rom c from fw v (tag v) Hc); try eassumption || reflexivity.
  - rewrite getr_other by reg_neq_tac. exact A10.
  - rewrite getr_other by reg_neq_tac. exact A11.
Qed.

(** THEOREM: a pointer to a forwarded object returns the forwarding address. *)
Theorem copy_value_forwarded : forall regs mem sp v fwd,
  cv_pre regs mem sp v -> is_ptr_tag (tag v) -> in_from from fw (ptr_of v) ->
  (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
  wat mem (ptr_of v) V_FORWARD -> wat mem (at_off (ptr_of v) 8) fwd ->
  returns regs rom mem (M mem) fwd.
Proof.
  intros regs mem sp v fwd Hpre Ht Hif Hb H0 H1.
  pose proof (minv_M regs mem sp v Hpre) as I. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (ptr_of v)) as Rp. change (bv_modulus 64) with (2^64)%Z in Rp.
  destruct (top_test regs mem sp v Hpre Ht Hif) as (Rt & Hm & T10 & T11 & T14 & T13 & T17 & T2 & Tk).
  assert (W0 : wat (M mem) (ptr_of v) V_FORWARD) by (apply heap_keep; [exact H0|lia|lia]).
  assert (W1 : wat (M mem) (at_off (ptr_of v) 8) fwd)
    by (apply heap_keep; [exact H1|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  destruct (body_forwarded (M mem) Rt (ptr_of v) fwd I T17 W0 W1) as (Rf & Hb2 & F11 & F2 & Fk).
  eapply (top_compose regs mem sp v (M mem) Rf Rt fwd Hpre Hm T2 Tk Hb2 F11 F2 Fk I).
Qed.

(** THEOREM: a pair whose tail isn't a pair is copied and forwarded. *)
Theorem copy_value_pair_leaf : forall regs mem sp v q w0 w1,
  cv_pre regs mem sp v -> tag v = 3%Z -> in_from from fw (ptr_of v) ->
  (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
  wat mem (ptr_of v) w0 -> w0 <> V_FORWARD -> wat mem (at_off (ptr_of v) 8) w1 ->
  wat mem (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  tag w1 <> 3%Z ->
  returns regs rom mem (pair_write (M mem) q (ptr_of v) w0 w1 (pair_moved q)) (pair_moved q).
Proof.
  intros regs mem sp v q w0 w1 Hpre Ht Hif Hb H0 Hne H1 Hnx Hq1 Hq2 Ht1.
  pose proof (minv_M regs mem sp v Hpre) as I. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (ptr_of v)) as Rp. change (bv_modulus 64) with (2^64)%Z in Rp.
  assert (Htp : is_ptr_tag (tag v)) by (rewrite Ht; right; left; reflexivity).
  destruct (top_test regs mem sp v Hpre Htp Hif) as (Rt & Hm & T10 & T11 & T14 & T13 & T17 & T2 & Tk).
  rewrite Ht in T14.
  destruct Hif as [Hif _].
  assert (W0 : wat (M mem) (ptr_of v) w0) by (apply heap_keep; [exact H0|lia|lia]).
  assert (W1 : wat (M mem) (at_off (ptr_of v) 8) w1)
    by (apply heap_keep; [exact H1|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  assert (Wn : wat (M mem) (at_off c 16) q)
    by (apply heap_keep; [exact Hnx|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  destruct (body_pair_leaf (M mem) Rt (ptr_of v) q w0 w1 I T10 T17 T14 ltac:(lia) Hb W0 Hne W1 Wn Hq1 Hq2 Ht1)
    as (Rf & Hb2 & F11 & F2 & Fk).
  eapply (top_compose regs mem sp v _ Rf Rt _ Hpre Hm T2 Tk Hb2 F11 F2 Fk).
  apply minv_pair_write; [exact I|lia|exact Hb|exact Hq1|exact Hq2].
Qed.

(** THEOREM: a pair whose tail is a pair: the spine is copied per the [spine] relation. *)
Theorem copy_value_pair_spine : forall regs mem sp v q w0 w1 m' cur',
  cv_pre regs mem sp v -> tag v = 3%Z -> in_from from fw (ptr_of v) ->
  (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
  wat mem (ptr_of v) w0 -> w0 <> V_FORWARD -> wat mem (at_off (ptr_of v) 8) w1 ->
  wat mem (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
  tag w1 = 3%Z ->
  spine (pair_write (M mem) q (ptr_of v) w0 w1 (pair_moved q)) (at_off q 16) w1 m' cur' ->
  returns regs rom mem m' (pair_moved q).
Proof.
  intros regs mem sp v q w0 w1 m' cur' Hpre Ht Hif Hb H0 Hne H1 Hnx Hq1 Hq2 Ht1 Hs.
  pose proof (minv_M regs mem sp v Hpre) as I. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (ptr_of v)) as Rp. change (bv_modulus 64) with (2^64)%Z in Rp.
  assert (Htp : is_ptr_tag (tag v)) by (rewrite Ht; right; left; reflexivity).
  destruct (top_test regs mem sp v Hpre Htp Hif) as (Rt & Hm & T10 & T11 & T14 & T13 & T17 & T2 & Tk).
  rewrite Ht in T14.
  destruct Hif as [Hif _].
  assert (W0 : wat (M mem) (ptr_of v) w0) by (apply heap_keep; [exact H0|lia|lia]).
  assert (W1 : wat (M mem) (at_off (ptr_of v) 8) w1)
    by (apply heap_keep; [exact H1|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  assert (Wn : wat (M mem) (at_off c 16) q)
    by (apply heap_keep; [exact Hnx|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  destruct (body_pair_spine (M mem) Rt (ptr_of v) q w0 w1 m' cur' I T10 T17 T14 T13 ltac:(lia) Hb W0 Hne W1 Wn Hq1 Hq2 Ht1 Hs)
    as (Rf & Hb2 & F11 & F2 & I2 & Fk).
  eapply (top_compose regs mem sp v m' Rf Rt _ Hpre Hm T2 Tk Hb2 F11 F2 Fk I2).
Qed.

Lemma minv_obj_write : forall m (q p : word) src n t,
  minv m -> (2 <= n)%Z ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 8 * n <= bv_unsigned tohi)%Z ->
  minv (obj_write m q p src n t).
Proof.
  intros m q p src n t I Hn Hp1 Hp2 Hq1 Hq2. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  unfold obj_write.
  apply minv_heap; [apply minv_heap; [apply minv_next|left; lia]|left; rewrite u_at_off by lia; lia].
  apply (minv_copy_from _ 2%Z _ q src n); [|lia|rewrite Z2Nat.id by lia; lia|exact Hq1|exact Hq2].
  apply minv_heap; [apply minv_heap; [exact I|right; lia]|right; rewrite u_at_off by lia; lia].
Qed.

(** THEOREM: any other object is copied whole and forwarded. *)
Theorem copy_value_object : forall regs mem sp v q h (src : Z -> word),
  cv_pre regs mem sp v -> (tag v = 1 \/ tag v = 5 \/ tag v = 6)%Z -> in_from from fw (ptr_of v) ->
  (forall j, (0 <= j < obj_words_Z (bv_unsigned h))%Z -> wat mem (at_off (ptr_of v) (8 * j)) (src j)) ->
  src 0%Z = h -> h <> V_FORWARD ->
  (1 <= hdr_type (bv_unsigned h) <= 11)%Z ->
  (bv_unsigned (ptr_of v) + 8 * obj_words_Z (bv_unsigned h) <= fromhi)%Z ->
  wat mem (at_off c 16) q ->
  (bv_unsigned q0 <= bv_unsigned q)%Z ->
  (bv_unsigned q + 8 * obj_words_Z (bv_unsigned h) <= bv_unsigned tohi)%Z ->
  returns regs rom mem
    (obj_write (M mem) q (ptr_of v) src (obj_words_Z (bv_unsigned h)) (tag v))
    (obj_moved (tag v) q).
Proof.
  intros regs mem sp v q h src Hpre Ht Hif Hs E0 Hne Hty Hb Hnx Hq1 Hq2.
  pose proof (minv_M regs mem sp v Hpre) as I. pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ (ptr_of v)) as Rp. change (bv_modulus 64) with (2^64)%Z in Rp.
  pose proof (obj_words_ge2 h Hty) as Hn2.
  assert (Htp : is_ptr_tag (tag v)) by (destruct Ht as [E|[E|E]]; rewrite E; unfold is_ptr_tag; lia).
  destruct (top_test regs mem sp v Hpre Htp Hif) as (Rt & Hm & T10 & T11 & T14 & T13 & T17 & T2 & Tk).
  destruct Hif as [Hif _].
  assert (Hs2 : forall j, (0 <= j < obj_words_Z (bv_unsigned h))%Z -> wat (M mem) (at_off (ptr_of v) (8 * j)) (src j)).
  { intros j Hj. apply heap_keep; [apply Hs; exact Hj|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]. }
  assert (Wn : wat (M mem) (at_off c 16) q)
    by (apply heap_keep; [exact Hnx|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia]).
  destruct (body_object (M mem) Rt (ptr_of v) q h src (tag v) I T10 T17 T14 Ht Hs2 E0 Hne Hty ltac:(lia) Hb Wn Hq1 Hq2)
    as (Rf & Hb2 & F11 & F2 & Fk).
  eapply (top_compose regs mem sp v _ Rf Rt _ Hpre Hm T2 Tk Hb2 F11 F2 Fk).
  apply minv_obj_write; [exact I|exact Hn2|lia|lia|exact Hq1|exact Hq2].
Qed.

(** What the copy leaves in memory. *)
Lemma obj_write_facts : forall m (q p : word) src n t,
  (2 <= n)%Z -> (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 8 * n <= bv_unsigned tohi)%Z ->
  (bv_unsigned from <= bv_unsigned p)%Z -> (bv_unsigned p + 16 <= fromhi)%Z ->
  let m' := obj_write m q p src n t in
  wat m' (at_off c 16) (at_off q (8 * n)) /\ wat m' p V_FORWARD /\ wat m' (at_off p 8) (obj_moved t q) /\
  (forall j, (0 <= j < n)%Z -> wat m' (at_off q (8 * j)) (src j)).
Proof.
  intros m q p src n t Hn Hq1 Hq2 Hp1 Hp2. cbv zeta.
  pose proof ranges as (R0 & R1 & R2 & R3).
  pose proof (bv_unsigned_in_range _ q) as Rc. pose proof (bv_unsigned_in_range _ p) as Rp.
  change (bv_modulus 64) with (2^64)%Z in Rc, Rp.
  assert (U16 : bv_unsigned (at_off c 16) = (bv_unsigned c + 16)%Z) by (apply u_at_off; lia).
  assert (Up8 : bv_unsigned (at_off p 8) = (bv_unsigned p + 8)%Z) by (apply u_at_off; lia).
  assert (Uq : forall j, (0 <= j < n)%Z -> bv_unsigned (at_off q (8 * j)) = (bv_unsigned q + 8 * j)%Z).
  { intros j Hj. apply u_at_off. lia. }
  unfold obj_write.
  set (mc := copy_from (wbytes (wbytes m q (w8 (src 0%Z))) (at_off q 8) (w8 (src 1%Z))) q src 2 (Z.to_nat (n - 2))).
  set (m1 := wbytes mc (at_off c 16) (w8 (at_off q (8 * n)))).
  set (m2 := wbytes m1 p (w8 V_FORWARD)).
  split; [|split; [|split]].
  - apply wat_other; [apply wat_other; [apply wat_hit; rewrite U16; lia|rewrite U16; unfold fromhi in *; lia|lia|rewrite U16; lia]
      |rewrite U16, Up8; unfold fromhi in *; lia|rewrite Up8; lia|rewrite U16; lia].
  - apply wat_other; [apply wat_hit; lia|rewrite Up8; lia|rewrite Up8; lia|lia].
  - apply wat_hit. rewrite Up8. lia.
  - intros j Hj.
    assert (Wc : wat mc (at_off q (8 * j)) (src j)).
    { destruct (Z_lt_le_dec j 2) as [Hl|Hg].
      - assert (Hdk : forall i, (2 <= i < 2 + Z.of_nat (Z.to_nat (n - 2)))%Z ->
          (bv_unsigned (at_off q (8 * i)) + 8 <= bv_unsigned (at_off q (8 * j)) \/
           bv_unsigned (at_off q (8 * j)) + 8 <= bv_unsigned (at_off q (8 * i)))%Z /\
          (bv_unsigned (at_off q (8 * i)) + 8 <= 2^64)%Z).
        { intros i Hi. rewrite Z2Nat.id in Hi by lia. rewrite !Uq by lia. split; lia. }
        apply copy_from_keeps; [|exact Hdk|rewrite Uq by lia; lia].
        assert (Ej : j = 0%Z \/ j = 1%Z) by lia.
        destruct Ej as [->| ->].
        + change (8 * 0)%Z with 0%Z. rewrite at_off_0.
          apply wat_other; [apply wat_hit; lia|rewrite u_at_off by lia; lia|rewrite u_at_off by lia; lia|lia].
        + change (8 * 1)%Z with 8%Z. apply wat_hit. rewrite u_at_off by lia. lia.
      - apply copy_from_wrote; [rewrite Z2Nat.id by lia; lia|lia|rewrite Z2Nat.id by lia; lia]. }
    apply wat_other; [apply wat_other; [apply wat_other; [exact Wc|rewrite U16; rewrite (Uq j Hj); lia|rewrite U16; lia|rewrite (Uq j Hj); lia]
      |rewrite (Uq j Hj); unfold fromhi in *; lia|lia|rewrite (Uq j Hj); lia]
      |rewrite (Uq j Hj), Up8; unfold fromhi in *; lia|rewrite Up8; lia|rewrite (Uq j Hj); lia].
Qed.

(** Copying only adds to what is mapped. *)
Lemma copy_from_grows : forall k (m : word -> option byte) q src i, mem_grows m (copy_from m q src i k).
Proof.
  induction k as [|k IH]; intros m q src i x Hx; [exact Hx|].
  cbn [copy_from]. apply (IH _ q src (i + 1)%Z x). refine (wbytes_grows _ _ _ x Hx).
Qed.

Lemma spine_write_grows : forall m cur p w0 w1, mem_grows m (spine_write m cur p w0 w1).
Proof.
  intros m cur p w0 w1 x Hx. unfold spine_write. cbv zeta.
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). exact Hx.
Qed.

Lemma spine_grows : forall m cur t m' cur', spine m cur t m' cur' -> mem_grows m m'.
Proof.
  induction 1; intros x Hx; try exact Hx.
  - apply spine_write_grows; exact Hx.
  - apply IHspine, spine_write_grows; exact Hx.
Qed.

Lemma pair_write_grows : forall m q p w0 w1 mv, mem_grows m (pair_write m q p w0 w1 mv).
Proof.
  intros m q p w0 w1 mv x Hx. unfold pair_write.
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). exact Hx.
Qed.

Lemma obj_write_grows : forall m q p src n t, mem_grows m (obj_write m q p src n t).
Proof.
  intros m q p src n t x Hx. unfold obj_write.
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _).
  refine (wbytes_grows _ _ _ x _). apply copy_from_grows.
  refine (wbytes_grows _ _ _ x _). refine (wbytes_grows _ _ _ x _). exact Hx.
Qed.

(** One call of [copy_value], as a relation; [M mem] is the memory with this call's frame. *)
Inductive cv_rel (mem : word -> option byte) (v : word) : (word -> option byte) -> word -> Prop :=
| cv_nonptr : non_ptr_tag (tag v) -> cv_rel mem v (M mem) v
| cv_forwarded : forall fwd,
    is_ptr_tag (tag v) -> in_from from fw (ptr_of v) ->
    (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
    wat mem (ptr_of v) V_FORWARD -> wat mem (at_off (ptr_of v) 8) fwd ->
    cv_rel mem v (M mem) fwd
| cv_pair_leaf : forall q w0 w1,
    tag v = 3%Z -> in_from from fw (ptr_of v) ->
    (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
    wat mem (ptr_of v) w0 -> w0 <> V_FORWARD -> wat mem (at_off (ptr_of v) 8) w1 ->
    wat mem (at_off c 16) q ->
    (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
    tag w1 <> 3%Z ->
    cv_rel mem v (pair_write (M mem) q (ptr_of v) w0 w1 (pair_moved q)) (pair_moved q)
| cv_pair_spine : forall q w0 w1 m' cur',
    tag v = 3%Z -> in_from from fw (ptr_of v) ->
    (bv_unsigned (ptr_of v) + 16 <= fromhi)%Z ->
    wat mem (ptr_of v) w0 -> w0 <> V_FORWARD -> wat mem (at_off (ptr_of v) 8) w1 ->
    wat mem (at_off c 16) q ->
    (bv_unsigned q0 <= bv_unsigned q)%Z -> (bv_unsigned q + 16 <= bv_unsigned tohi)%Z ->
    tag w1 = 3%Z ->
    spine (pair_write (M mem) q (ptr_of v) w0 w1 (pair_moved q)) (at_off q 16) w1 m' cur' ->
    cv_rel mem v m' (pair_moved q)
| cv_object : forall q h (src : Z -> word),
    (tag v = 1 \/ tag v = 5 \/ tag v = 6)%Z -> in_from from fw (ptr_of v) ->
    (forall j, (0 <= j < obj_words_Z (bv_unsigned h))%Z -> wat mem (at_off (ptr_of v) (8 * j)) (src j)) ->
    src 0%Z = h -> h <> V_FORWARD ->
    (1 <= hdr_type (bv_unsigned h) <= 11)%Z ->
    (bv_unsigned (ptr_of v) + 8 * obj_words_Z (bv_unsigned h) <= fromhi)%Z ->
    wat mem (at_off c 16) q ->
    (bv_unsigned q0 <= bv_unsigned q)%Z ->
    (bv_unsigned q + 8 * obj_words_Z (bv_unsigned h) <= bv_unsigned tohi)%Z ->
    cv_rel mem v (obj_write (M mem) q (ptr_of v) src (obj_words_Z (bv_unsigned h)) (tag v))
      (obj_moved (tag v) q).

(** THEOREM: every [copy_value] call that satisfies its relation runs and returns. *)
Theorem copy_value_contract : forall regs mem sp v m' res,
  cv_pre regs mem sp v -> cv_rel mem v m' res ->
  returns regs rom mem m' res /\ minv m' /\ mem_grows mem m'.
Proof.
  intros regs mem sp v m' res Hpre Hr.
  pose proof (minv_M regs mem sp v Hpre) as I.
  pose proof Hpre as (Hc & A2 & Efp & Hst & Hw & A1 & A8 & A9 & A18 & A19 & Hev & A10 & A11 & _).
  assert (Hg : mem_grows mem (M mem)) by (unfold M; apply push_grows).
  pose proof ranges as (R0 & R1 & R2 & R3).
  destruct Hr.
  - split; [|split; [exact I|exact Hg]].
    pose proof (copy_value_nonptr regs mem rom sp Hc A2 Hst Hw) as T.
    rewrite A1 in T. specialize (T Hev). rewrite A11 in T. specialize (T H).
    rewrite <- Efp in T. rewrite A8, A9, A18, A19 in T. exact T.
  - split; [eapply copy_value_forwarded; eassumption|split; [exact I|exact Hg]].
  - assert (Ri : (bv_unsigned from <= bv_unsigned (ptr_of v))%Z) by (destruct H0; lia).
    split; [eapply copy_value_pair_leaf; eassumption|split].
    + apply minv_pair_write; assumption.
    + intros x Hx. apply pair_write_grows, Hg, Hx.
  - assert (Ri : (bv_unsigned from <= bv_unsigned (ptr_of v))%Z) by (destruct H0; lia).
    pose proof (minv_pair_write (M mem) q (ptr_of v) w0 w1 (pair_moved q) I Ri H1 H6 H7) as I2.
    split; [eapply copy_value_pair_spine; eassumption|split].
    + eapply spine_minv; eassumption.
    + intros x Hx. apply (spine_grows _ _ _ _ _ H9), pair_write_grows, Hg, Hx.
  - assert (Ri : (bv_unsigned from <= bv_unsigned (ptr_of v))%Z) by (destruct H0; lia).
    pose proof (obj_words_ge2 h H4) as Hn2.
    split; [eapply copy_value_object; eassumption|split].
    + apply minv_obj_write; [exact I|exact Hn2|exact Ri|lia|exact H7|exact H8].
    + intros x Hx. apply obj_write_grows, Hg, Hx.
Qed.

End Layout.
