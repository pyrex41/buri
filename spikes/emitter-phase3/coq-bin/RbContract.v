(** * [run_block] on its compiled bytes (0x3d77a): the loop, a slice of its cases.

    The loop head is 0x3d7d4.  [LH] is the loop invariant: the registers the loop keeps (o in s0,
    fuel in s10, x in s4, out in s5, stop in a4), the frame slots, the context fields, the code
    bytes, and [sym_at]: the [Sym] at [y] holds the abstract [Y].  [sd_iter] is one trip of the loop
    for an [sd]: the bounds checks, the call to [decode] (through its contract, [Hdec]), the
    dispatch through the jump table, the recorded store, and the jump back.  Proof-side only. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk MemSplit.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import s9bin_code BinGcStep BinMoveStep BinGcTac BinGcMem BinRun BinMem BinBits DecSpec DecPost RbSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.

Abbreviation W z := (Z_to_bv 64 z).

(** ** Words, branches and reads, by numbers *)

Lemma uW : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (W z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.

Lemma bt_eq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_EQ (W a) (W b) = (a =? b).
Proof. intros. cbn [branch_taken]. unfold bv_eqb. rewrite !uW by lia. reflexivity. Qed.
Lemma bt_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_NE (W a) (W b) = negb (a =? b).
Proof. intros. cbn [branch_taken]. unfold bv_eqb. rewrite !uW by lia. reflexivity. Qed.
Lemma bt_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_LTU (W a) (W b) = (a <? b).
Proof. intros. cbn [branch_taken]. unfold bv_ltu. rewrite !uW by lia. reflexivity. Qed.

Lemma rdn_inside : forall segs n bs (m : mem) (A : word) k,
  bv_unsigned A + Z.of_nat (length bs) <= 2 ^ 64 -> (k + n <= length bs)%nat ->
  rdn segs (wbytes m A bs) (v_addi A (Z.of_nat k)) n = Some (firstn n (skipn k bs)).
Proof.
  intros segs n. induction n as [|n IH]; intros bs m A k Hb Hk; [reflexivity|].
  cbn [rdn]. rewrite wbytes_inside.
  2: lia.
  2: rewrite u_addi by (pose proof (bv_unsigned_in_range _ A); change (bv_modulus 64) with (2^64) in *; lia); lia.
  rewrite u_addi by (pose proof (bv_unsigned_in_range _ A); change (bv_modulus 64) with (2^64) in *; lia).
  replace (bv_unsigned A + Z.of_nat k - bv_unsigned A) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  replace (v_addi A (Z.of_nat k) + 1)%bv with (v_addi A (Z.of_nat (S k))).
  2: { apply bv_eq. unfold v_addi. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1.
       rewrite Nat2Z.inj_succ. unfold bv_wrap. rewrite Z.add_mod_idemp_l by (cbv; discriminate). f_equal. lia. }
  rewrite IH by lia.
  destruct (skipn k bs) as [|b r] eqn:E.
  - exfalso. pose proof (f_equal (@length _) E) as L. rewrite length_skipn in L. cbn in L. lia.
  - replace (nth k bs (Z_to_bv 8 0)) with (nth 0 (skipn k bs) (Z_to_bv 8 0)) by (rewrite nth_skipn, Nat.add_0_r; reflexivity).
    replace (skipn (S k) bs) with r by (replace (S k) with (1 + k)%nat by lia; rewrite <- skipn_skipn, E; reflexivity).
    rewrite E. reflexivity.
Qed.

Lemma vW : forall z k, 0 <= z < 2 ^ 64 -> v_addi (W z) k = W (z + k).
Proof. intros. unfold v_addi. rewrite uW by lia. reflexivity. Qed.

Lemma lw_small : forall z, 0 <= z < 2 ^ 31 -> v_lw (W z) = W z.
Proof.
  intros z Hz. unfold v_lw. rewrite uW by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma le4_val : forall z, 0 <= z < 2 ^ 32 -> bytes_le_to_Z (lebytes 4 z) = bv_unsigned (W z).
Proof.
  intros z Hz. unfold lebytes. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  rewrite uW by lia. apply Z.mod_small. lia.
Qed.

Lemma le8_val : forall z, bytes_le_to_Z (lebytes 8 z) = bv_unsigned (W z).
Proof. intros z. unfold lebytes. apply bytes_le_to_Z_8. Qed.

(** Fields of [Ins] in its bytes. *)
Lemma f_k : forall i, firstn 4 (skipn 0 (encb i)) = lebytes 4 (ik i). Proof. reflexivity. Qed.
Lemma f_rd : forall i, firstn 4 (skipn 4 (encb i)) = lebytes 4 (ird i). Proof. reflexivity. Qed.
Lemma f_r1 : forall i, firstn 4 (skipn 8 (encb i)) = lebytes 4 (ir1 i). Proof. reflexivity. Qed.
Lemma f_r2 : forall i, firstn 4 (skipn 12 (encb i)) = lebytes 4 (ir2 i). Proof. reflexivity. Qed.
Lemma f_imm : forall i, firstn 8 (skipn 16 (encb i)) = lebytes 8 (iimm i). Proof. reflexivity. Qed.
Lemma f_len : forall i, firstn 4 (skipn 24 (encb i)) = lebytes 4 (ilen i). Proof. reflexivity. Qed.

Definition ins_ok (i : ins) : Prop :=
  0 <= ik i <= 15 /\ 0 <= ird i < 32 /\ 0 <= ir1 i < 32 /\ 0 <= ir2 i < 32 /\ (ilen i = 2 \/ ilen i = 4).

(** ** The memory-resident state *)

Definition pack (x : av) : Z := avb x + ava x * 2 ^ 32.
Definition av_ok (x : av) : Prop := 0 <= avb x <= 13 /\ 0 <= ava x < 2 ^ 32 /\ 0 <= avk x < 2 ^ 64.
(** An [AV] at [base + off]: its packed b and a, then k. *)
Definition av_at (m : mem) (b : word) (off : Z) (x : av) : Prop :=
  wat m (v_addi b off) (W (pack x)) /\ wat m (v_addi b (off + 8)) (W (avk x)).
Definition w4at (m : mem) (A : word) (z : Z) : Prop := rdn source_segs m A 4 = Some (lebytes 4 z).

Definition sym_at (m : mem) (y : word) (Y : sym) : Prop :=
  0 <= ynw Y <= 16 /\
  (forall i, 0 <= i < 32 -> av_ok (yr Y i) /\ av_at m y (16 * i) (yr Y i)) /\
  (forall j, 0 <= j < ynw Y -> av_ok (fst (yw Y j)) /\ av_ok (snd (yw Y j)) /\
       av_at m y (512 + 32 * j) (fst (yw Y j)) /\ av_at m y (528 + 32 * j) (snd (yw Y j))) /\
  w4at m (v_addi y 1024) (ynw Y).

(** Reads inside [lo, hi) don't see memory outside it. *)
Definition same_in (m m' : mem) (lo hi : Z) : Prop := forall a : word, lo <= bv_unsigned a < hi -> m' a = m a.

Lemma wat_same : forall m m' (A v : word) lo hi, same_in m m' lo hi -> lo <= bv_unsigned A -> bv_unsigned A + 8 <= hi ->
  hi <= 2 ^ 64 -> wat m A v -> wat m' A v.
Proof. intros. unfold wat in *. rewrite (rdn_ext _ _ m' m) by (cbn; lia || (intros; apply H; cbn in *; lia)). exact H3. Qed.

Lemma w4_same : forall m m' (A : word) z lo hi, same_in m m' lo hi -> lo <= bv_unsigned A -> bv_unsigned A + 4 <= hi ->
  hi <= 2 ^ 64 -> w4at m A z -> w4at m' A z.
Proof. intros. unfold w4at in *. rewrite (rdn_ext _ _ m' m) by (cbn; lia || (intros; apply H; cbn in *; lia)). exact H3. Qed.

(** ** Tactics for the loop *)

(* A 64-bit load of a [wat] fact. *)
Ltac ld8 Fw := let n := pc_of in fd n ltac:(fun F D =>
  eapply rm_step; [reflexivity | eapply z_ld_at; [wxf F | reflexivity | exact D | reflexivity
    | gres; rsub; imm_norm; reflexivity | exact Fw | apply bytes8] | norm_rm]).

(* A 32-bit signed load of a 4-byte fact [rdn _ a 4 = Some (lebytes 4 z)], z small. *)
Ltac lw4 Fw := let n := pc_of in fd n ltac:(fun F D =>
  eapply rm_step; [reflexivity | eapply z_lw_at; [wxf F | reflexivity | exact D | reflexivity
    | gres; rsub; imm_norm; reflexivity | exact Fw | apply le4_val; lia] | norm_rm]).

Ltac st1 := let n := pc_of in fd n ltac:(fun F D => astep_with F D ltac:(fun _ _ => fail) ltac:(fun _ _ => fail)).

Lemma addr_code : forall c o k, 0 <= c -> 0 <= o -> 0 <= k -> c + o + k < 2 ^ 64 ->
  v_addi (v_add (W 0) (v_add (W c) (W o))) k = v_addi (W c) (o + k).
Proof.
  intros. apply bv_eq. unfold v_addi, v_add. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 c), (bv_wrap_small 64 o) by (change (bv_modulus 64) with (2^64); lia).
  rewrite (bv_wrap_small 64 (c + o)) by (change (bv_modulus 64) with (2^64); lia).
  change (bv_wrap 64 0) with 0. rewrite Z.add_0_l.
  rewrite (bv_wrap_small 64 (c + o)) by (change (bv_modulus 64) with (2^64); lia).
  f_equal; lia.
Qed.

Lemma addr_idx : forall (b : word) n s, 0 <= n -> 0 <= s <= 6 -> n * 2 ^ s < 2 ^ 63 ->
  v_add (v_slli (W n) s) b = v_addi b (n * 2 ^ s).
Proof.
  intros. apply bv_eq. unfold v_addi, v_add, v_slli. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 n) by (change (bv_modulus 64) with (2^64); nia).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (bv_wrap_small 64 (n * 2 ^ s)) by (change (bv_modulus 64) with (2^64); nia).
  f_equal. lia.
Qed.

Lemma rd_out : forall segs (m m1 : mem) (A a : word) bs n, meq m1 (wbytes m A bs) ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned A \/ bv_unsigned A + Z.of_nat (length bs) <= bv_unsigned a) ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 -> bv_unsigned A + Z.of_nat (length bs) <= 2 ^ 64 ->
  rdn segs m1 a n = rdn segs m a n.
Proof.
  intros segs m m1 A a bs n H Hd H1 H2. rewrite (rdn_ext segs n m1 (wbytes m A bs)) by (try lia; intros; apply H).
  apply rdn_wbytes_out; assumption.
Qed.

Lemma clear_meq : forall (m m1 : mem) (A : word) bs, meq m1 (wbytes m A bs) -> mem_clear m TL TH ->
  TH <= bv_unsigned A -> bv_unsigned A + Z.of_nat (length bs) <= 2 ^ 64 -> mem_clear m1 TL TH.
Proof.
  intros m m1 A bs H Hc H1 H2 a Ha. rewrite H. apply (mem_clear_wbytes m A bs TL TH Hc); [left; lia | lia | exact Ha].
Qed.

Lemma writable_meq : forall (m m1 : mem) (A : word) bs lo hi, meq m1 (wbytes m A bs) -> writable m lo hi ->
  writable m1 lo hi.
Proof.
  intros m m1 A bs lo hi H Hw a Ha.
  assert (E : wview source_segs m1 a = wview source_segs (wbytes m A bs) a) by (unfold wview; rewrite (H a); reflexivity).
  rewrite E. exact (writable_store m lo hi A bs Hw a Ha).
Qed.

Lemma sym_addr : forall (b : word) r s k, 0 <= r -> 0 <= s <= 6 -> 0 <= k -> bv_unsigned b + r * 2 ^ s + k < 2 ^ 64 ->
  v_addi (v_add (v_slli (W r) s) b) k = v_addi b (r * 2 ^ s + k).
Proof.
  intros b r s k Hr Hs Hk Hb. apply bv_eq. unfold v_addi, v_add, v_slli. rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ b). change (bv_modulus 64) with (2^64) in *.
  assert (r * 2 ^ s < 2 ^ 64) by (pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)); nia).
  rewrite (bv_wrap_small 64 r) by (change (bv_modulus 64) with (2^64); nia).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (bv_wrap_small 64 (r * 2 ^ s)) by (change (bv_modulus 64) with (2^64); lia).
  rewrite (bv_wrap_small 64 (r * 2 ^ s + bv_unsigned b)) by (change (bv_modulus 64) with (2^64); lia).
  f_equal. lia.
Qed.

Lemma uadd : forall a b : word, bv_unsigned a + bv_unsigned b < 2 ^ 64 -> bv_unsigned (v_add a b) = bv_unsigned a + bv_unsigned b.
Proof. intros. unfold v_add. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64).
  pose proof (bv_unsigned_in_range _ a). pose proof (bv_unsigned_in_range _ b). change (bv_modulus 64) with (2^64) in *. lia. Qed.

Lemma uslli : forall n s, 0 <= n -> 0 <= s -> n * 2 ^ s < 2 ^ 64 -> bv_unsigned (v_slli (W n) s) = n * 2 ^ s.
Proof.
  intros. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  assert (n * 1 <= n * 2 ^ s) by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite (uW n) by lia. rewrite Z.shiftl_mul_pow2 by lia. apply uW. lia.
Qed.

Lemma vadd_W : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> v_add (W a) (W b) = W (a + b).
Proof. intros. unfold v_add. rewrite !uW by lia. reflexivity. Qed.

Lemma addiw_W : forall a k, 0 <= a + k < 2 ^ 31 -> 0 <= a < 2 ^ 31 -> v_addiw (W a) k = W (a + k).
Proof.
  intros. unfold v_addiw. rewrite uW by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma pack_ok : forall v, av_ok v -> 0 <= pack v < 2 ^ 64.
Proof. intros v (H1 & H2 & H3). unfold pack. lia. Qed.

Lemma sextw_pack : forall v, av_ok v -> v_addiw (W (pack v)) 0 = W (avb v).
Proof.
  intros v (H1 & H2 & H3). unfold v_addiw. rewrite uW by (unfold pack; lia). f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). unfold pack.
  rewrite Z.add_0_r. replace (avb v + ava v * 2 ^ 32 + 2 ^ 31) with ((avb v + 2 ^ 31) + ava v * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* An infeasible branch: its condition contradicts the facts. *)
Ltac kill :=
  try (exfalso; match goal with Hbr : branch_taken _ _ _ = _ |- _ =>
         first [ (lazymatch type of Hbr with ?L = _ => check_closed_term L end; vm_compute in Hbr; discriminate)
               | rewrite ?vW, ?addiw_W in Hbr by lia; rewrite ?bt_eq, ?bt_ne, ?bt_ltu in Hbr by lia; cbn [negb] in Hbr;
                 first [apply Z.eqb_eq in Hbr | apply Z.eqb_neq in Hbr | apply Z.ltb_lt in Hbr | apply Z.ltb_ge in Hbr
                       | apply negb_true_iff, Z.eqb_neq in Hbr | apply negb_false_iff, Z.eqb_eq in Hbr]; lia ] end).


Section Loop.
Context {fx : FPState}.
Variables (rom : mem) (ra0 sp x y out : word) (stop code len : Z) (bytes : Z -> Z) (E : env).

(** Layout: the frame, the [Sym], the context and the code are disjoint, above the text and rodata,
    and don't wrap. *)
Hypothesis Lsp : TH <= bv_unsigned sp /\ bv_unsigned sp + 352 <= 2 ^ 64.
Hypothesis Ly : TH <= bv_unsigned y /\ bv_unsigned y + 1032 <= 2 ^ 64.
Hypothesis Lx : bv_unsigned x + 184 <= 2 ^ 64.
Hypothesis Lc : 0 <= code /\ code + len <= 2 ^ 64.
Hypothesis Dspy : bv_unsigned sp + 352 <= bv_unsigned y \/ bv_unsigned y + 1032 <= bv_unsigned sp.
Hypothesis Dxy : bv_unsigned x + 184 <= bv_unsigned y \/ bv_unsigned y + 1032 <= bv_unsigned x.
Hypothesis Dxi : bv_unsigned x + 184 <= bv_unsigned sp + 216 \/ bv_unsigned sp + 248 <= bv_unsigned x.
Hypothesis Dcy : code + len <= bv_unsigned y \/ bv_unsigned y + 1032 <= code.
Hypothesis Dci : code + len <= bv_unsigned sp + 216 \/ bv_unsigned sp + 248 <= code.
Hypothesis Hstop : 0 <= stop < 2 ^ 63.
Hypothesis Hlen : 0 <= len < 2 ^ 63.
Hypothesis Hbytes : forall k, 0 <= bytes k < 256.

(** [decode]'s contract, as [DecContract] states it, for all four-byte inputs.  [decode16_contract]
    proves it when the low two bits of p[0] are not 11. *)
Hypothesis Hdec : forall (R0 : bvmap 5 word) (m0 : mem) b0 b1 b2 b3,
  mem_clear m0 TL TH -> writable m0 (bv_unsigned (getr R0 10)) (bv_unsigned (getr R0 10) + 32) ->
  TH <= bv_unsigned (getr R0 10) -> bv_unsigned (getr R0 10) + 32 <= 2 ^ 64 ->
  bv_unsigned (getr R0 1) mod 2 = 0 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  rdn source_segs m0 (v_addi (getr R0 11) 0) 1 = Some [Z_to_bv 8 b0] ->
  rdn source_segs m0 (v_addi (getr R0 11) 1) 1 = Some [Z_to_bv 8 b1] ->
  rdn source_segs m0 (v_addi (getr R0 11) 2) 1 = Some [Z_to_bv 8 b2] ->
  rdn source_segs m0 (v_addi (getr R0 11) 3) 1 = Some [Z_to_bv 8 b3] ->
  RunM (getr R0 1) rom (dpost R0 m0 (cdec b0 b1 b2 b3)) (mkst R0 (Z_to_bv 64 0x3e91e) m0 rom).

Hypothesis Hins : forall b0 b1 b2 b3, ins_ok (cdec b0 b1 b2 b3).

(** What the loop reads outside the [Sym] and the [Ins] buffer. *)
Definition frame_ok (m : mem) : Prop :=
  wat m (v_addi sp 64) (W stop) /\ wat m (v_addi sp 72) (W 0x50da8) /\ wat m (v_addi sp 80) y /\
  wat m (v_addi x 0) (W code) /\ wat m (v_addi x 8) (W len) /\
  (forall k, 0 <= k < len -> rdn source_segs m (v_addi (W code) k) 1 = Some [Z_to_bv 8 (bytes k)]).

Definition LH (o fuel : Z) (Y : sym) (regs : bvmap 5 word) (m : mem) : Prop :=
  getr regs 2 = sp /\ getr regs 8 = W o /\ getr regs 14 = W stop /\ getr regs 20 = x /\ getr regs 26 = W fuel /\
  0 <= o < 2 ^ 63 /\ 1 <= fuel <= 64 /\
  mem_clear m TL TH /\
  writable m (bv_unsigned (v_addi sp 216)) (bv_unsigned (v_addi sp 216) + 32) /\
  writable m (bv_unsigned y) (bv_unsigned y + 1032) /\
  frame_ok m /\ sym_at m y Y.

Lemma frame_same : forall m m', frame_ok m ->
  (forall a : word, ~ (bv_unsigned y <= bv_unsigned a < bv_unsigned y + 1032) ->
                    ~ (bv_unsigned sp + 216 <= bv_unsigned a < bv_unsigned sp + 248) -> m' a = m a) ->
  frame_ok m'.
Proof.
  intros m m' (F1 & F2 & F3 & F4 & F5 & F6) H.
  pose proof (bv_unsigned_in_range _ sp) as Rsp. pose proof (bv_unsigned_in_range _ x) as Rx.
  change (bv_modulus 64) with (2^64) in *.
  assert (Us : forall k, 0 <= k < 352 -> bv_unsigned (v_addi sp k) = bv_unsigned sp + k) by (intros; apply u_addi; lia).
  assert (Ux : forall k, 0 <= k < 184 -> bv_unsigned (v_addi x k) = bv_unsigned x + k) by (intros; apply u_addi; lia).
  unfold frame_ok, wat in *. repeat split.
  - rewrite (rdn_ext _ _ m' m); [exact F1| rewrite Us; lia |]. intros a Ha. rewrite Us in Ha by lia. apply H; lia.
  - rewrite (rdn_ext _ _ m' m); [exact F2| rewrite Us; lia |]. intros a Ha. rewrite Us in Ha by lia. apply H; lia.
  - rewrite (rdn_ext _ _ m' m); [exact F3| rewrite Us; lia |]. intros a Ha. rewrite Us in Ha by lia. apply H; lia.
  - rewrite (rdn_ext _ _ m' m); [exact F4| rewrite Ux; lia |]. intros a Ha. rewrite Ux in Ha by lia. apply H; lia.
  - rewrite (rdn_ext _ _ m' m); [exact F5| rewrite Ux; lia |]. intros a Ha. rewrite Ux in Ha by lia. apply H; lia.
  - intros k Hk. rewrite (rdn_ext _ _ m' m); [apply F6; lia| rewrite vW, uW by lia; cbn; lia |].
    intros a Ha. rewrite vW, uW in Ha by lia. cbn in Ha. apply H; lia.
Qed.

Lemma Uy0 : forall k, 0 <= k < 1032 -> bv_unsigned (v_addi y k) = bv_unsigned y + k.
Proof. intros; apply u_addi; pose proof (bv_unsigned_in_range _ y); change (bv_modulus 64) with (2^64) in *; lia. Qed.

Lemma sym_same : forall m m' Y, sym_at m y Y ->
  (forall a : word, bv_unsigned y <= bv_unsigned a < bv_unsigned y + 1032 -> m' a = m a) -> sym_at m' y Y.
Proof.
  intros m m' Y (Hn & Hr & Hw & H4) H. pose proof Ly.
  assert (T : forall k n v, 0 <= k -> (0 < n)%nat -> k + Z.of_nat n <= 1032 -> rdn source_segs m (v_addi y k) n = Some v ->
                            rdn source_segs m' (v_addi y k) n = Some v).
  { intros k n v Hk Hn0 Hkn R. rewrite (rdn_ext _ n m' m); [exact R | rewrite Uy0 by lia; lia |].
    intros a Ha. rewrite Uy0 in Ha by lia. apply H. lia. }
  unfold sym_at, av_at, wat, w4at in *. split; [exact Hn|]. split; [|split].
  - intros i Hi. destruct (Hr i Hi) as (O & A & B). split; [exact O|]. split; apply T; try lia; assumption.
  - intros j Hj. destruct (Hw j Hj) as (O1 & O2 & (A1 & B1) & (A2 & B2)).
    split; [exact O1|]. split; [exact O2|]. split; split; apply T; try lia; assumption.
  - apply T; try lia; assumption.
Qed.

Ltac rout := rewrite rdn_wbytes_out; [ | rewrite ?length_word_to_le_bytes, ?Uy0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia
                                       | rewrite ?Uy0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia
                                       | rewrite ?length_word_to_le_bytes, ?Uy0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia ].

(** The five stores of an [sd]'s record, in the compiled order, make [Y] with the new store. *)
Definition sd_mem (m : mem) (n : Z) (v1 v2 : av) : mem :=
  wbytes (wbytes (wbytes (wbytes (wbytes m (v_addi y (512 + 32 * n)) (w8 (W (pack v1))))
    (v_addi y (512 + 32 * n + 8)) (w8 (W (avk v1)))) (v_addi y 1024) (word_to_le_bytes 4 (W (n + 1))))
    (v_addi y (512 + 32 * n + 16)) (w8 (W (pack v2)))) (v_addi y (512 + 32 * n + 24)) (w8 (W (avk v2))).

Lemma sd_sym : forall m Y v1 v2, sym_at m y Y -> ynw Y < 16 -> av_ok v1 -> av_ok v2 ->
  sym_at (sd_mem m (ynw Y) v1 v2) y (Sym (yr Y) (upd (yw Y) (ynw Y) (v1, v2)) (ynw Y + 1)).
Proof.
  intros m Y v1 v2 (Hn & Hr & Hw & H4) Hlt O1 O2. pose proof Ly. unfold sd_mem, sym_at, av_at, wat, w4at in *.
  cbn [yr yw ynw]. split; [lia|]. split; [|split].
  - intros i Hi. destruct (Hr i Hi) as (O & A & B). split; [exact O|]. split; do 5 rout; assumption.
  - intros j Hj. unfold upd. destruct (Z.eqb_spec j (ynw Y)) as [->|Hne]; cbn [fst snd].
    + split; [exact O1|]. split; [exact O2|]. split; split.
      * do 4 rout. apply rdn_wbytes_hit8. rewrite Uy0 by lia. lia.
      * do 3 rout. replace (512 + 32 * ynw Y + 8) with (512 + 32 * ynw Y + 8) by lia. apply rdn_wbytes_hit8. rewrite Uy0 by lia. lia.
      * do 1 rout. replace (528 + 32 * ynw Y) with (512 + 32 * ynw Y + 16) by lia. apply rdn_wbytes_hit8. rewrite Uy0 by lia. lia.
      * replace (528 + 32 * ynw Y + 8) with (512 + 32 * ynw Y + 24) by lia. apply rdn_wbytes_hit8. rewrite Uy0 by lia. lia.
    + destruct (Hw j ltac:(lia)) as (P1 & P2 & (A1 & B1) & (A2 & B2)).
      split; [exact P1|]. split; [exact P2|]. split; split; do 5 rout; assumption.
  - do 2 rout. apply (rdn_wbytes_hit source_segs (word_to_le_bytes 4 (W (ynw Y + 1)))). rewrite length_word_to_le_bytes, Uy0 by lia. cbn. lia.
Qed.

(** One trip of the loop, up to the dispatch: the loop head's two exits are not taken, the bounds
    hold, [decode] runs, its fields are read, the operand registers [r1] and [r2] are loaded from
    the [Sym], and the jump table sends kind 9 ([I_SD]) to 0x3da52.  [Kd] is what happens there. *)
Lemma dispatch_sd : forall o fuel Y regs m Post,
  LH o fuel Y regs m -> o <> stop -> o <= stop -> o + 4 <= len ->
  let i := cdec (bytes o) (bytes (o + 1)) (bytes (o + 2)) (bytes (o + 3)) in
  ik i = I_SD ->
  (forall regs' m', getr regs' 2 = sp -> getr regs' 8 = W o -> getr regs' 20 = x -> getr regs' 26 = W fuel ->
     getr regs' 23 = W (pack (yr Y (ir1 i))) -> getr regs' 25 = W (avk (yr Y (ir1 i))) ->
     getr regs' 27 = W (pack (yr Y (ir2 i))) -> getr regs' 24 = W (avk (yr Y (ir2 i))) ->
     mem_clear m' TL TH -> writable m' (bv_unsigned (v_addi sp 216)) (bv_unsigned (v_addi sp 216) + 32) ->
     writable m' (bv_unsigned y) (bv_unsigned y + 1032) -> frame_ok m' -> sym_at m' y Y ->
     rdn source_segs m' (v_addi sp 232) 8 = Some (lebytes 8 (iimm i)) ->
     rdn source_segs m' (v_addi sp 240) 4 = Some (lebytes 4 (ilen i)) ->
     RunM ra0 rom Post (mkst regs' (W 0x3da52) m' rom)) ->
  RunM ra0 rom Post (mkst regs (W 0x3d7d4) m rom).
Proof.
  intros o fuel Y regs m Post HL Hne Hle Hb i Hk Kd.
  destruct HL as (R2 & R8 & R14 & R20 & R26 & Ho & Hfu & Hc & Hwi & Hwy & Fr & Sy).
  pose proof Fr as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (Hins (bytes o) (bytes (o + 1)) (bytes (o + 2)) (bytes (o + 3))) as Hi. fold i in Hi.
  destruct Hi as (Ik & Ird & Ir1 & Ir2 & Il).
  pose proof (bv_unsigned_in_range _ sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  norm_rm.
  st1; kill. st1; kill.                 (* beq s0,a4 ; bltu a4,s0 *)
  ld8 F5. st1. st1; kill.               (* ld s6,8(s4) ; addi ; bltu s6,a0 *)
  ld8 F4. st1. st1. st1. st1.           (* ld s1,0(s4) ; add ; addi a0,sp,216 ; mv a1,s1 ; auipc ra *)
  (* jalr 300(ra): the call *)
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_call with (tgt := W 0x3e91e); [wxf F | reflexivity | exact D | reflexivity
      | gres; apply bv_eq; vm_compute; reflexivity | reflexivity] | ]).
  eapply rm_call.
  { eapply (Hdec _ m (bytes o) (bytes (o + 1)) (bytes (o + 2)) (bytes (o + 3))).
    - exact Hc.
    - gres; rsub. exact Hwi.
    - gres; rsub. rewrite u_addi by lia. lia.
    - gres; rsub. rewrite u_addi by lia. lia.
    - gres. vm_compute. reflexivity.
    - apply Hbytes. - apply Hbytes. - apply Hbytes. - apply Hbytes.
    - gres; rsub. rewrite addr_code by lia. rewrite Z.add_0_r. apply F6. lia.
    - gres; rsub. rewrite addr_code by lia. apply F6. lia.
    - gres; rsub. rewrite addr_code by lia. apply F6. lia.
    - gres; rsub. rewrite addr_code by lia. apply F6. lia. }
  intros regs1 m1 [Kk Km]. fold i in Km. gres_in Km; rsub_in Km.
  assert (K2 : getr regs1 2 = sp) by (rewrite Kk by (repeat split; reg_neq_tac); gres; rsub; reflexivity).
  assert (K8 : getr regs1 8 = W o) by (rewrite Kk by (repeat split; reg_neq_tac); gres; rsub; reflexivity).
  assert (K20 : getr regs1 20 = x) by (rewrite Kk by (repeat split; reg_neq_tac); gres; rsub; reflexivity).
  assert (K26 : getr regs1 26 = W fuel) by (rewrite Kk by (repeat split; reg_neq_tac); gres; rsub; reflexivity).
  clear R2 R8 R14 R20 R26 Kk.
  assert (Us : forall k, 0 <= k < 352 -> bv_unsigned (v_addi sp k) = bv_unsigned sp + k) by (intros; apply u_addi; lia).
  assert (Uy : forall k, 0 <= k < 1032 -> bv_unsigned (v_addi y k) = bv_unsigned y + k)
    by (intros; apply u_addi; pose proof (bv_unsigned_in_range _ y); change (bv_modulus 64) with (2^64) in *; lia).
  assert (Hc1 : mem_clear m1 TL TH) by (eapply clear_meq; [exact Km | exact Hc | rewrite Us; lia | rewrite Us; cbn; lia]).
  clear Hc.
  (* what the dispatch reads *)
  assert (Rd : forall k n, (k + n <= 32)%nat -> rdn source_segs m1 (v_addi sp (216 + Z.of_nat k)) n = Some (firstn n (skipn k (encb i)))).
  { intros k n Hkn. rewrite (rdn_ext _ n m1 (wbytes m (v_addi sp 216) (encb i))) by (try (rewrite Us; lia); intros; apply Km).
    replace (v_addi sp (216 + Z.of_nat k)) with (v_addi (v_addi sp 216) (Z.of_nat k)).
    - apply rdn_inside; [rewrite Us; cbn; lia | exact Hkn].
    - apply bv_eq. rewrite !u_addi; try lia; rewrite ?Us; lia. }
  assert (Rk : rdn source_segs m1 (v_addi sp 216) 4 = Some (lebytes 4 (ik i))) by (rewrite <- f_k; exact (Rd 0%nat 4%nat ltac:(lia))).
  assert (Rr1 : rdn source_segs m1 (v_addi sp 224) 4 = Some (lebytes 4 (ir1 i))) by (rewrite <- f_r1; exact (Rd 8%nat 4%nat ltac:(lia))).
  assert (Rr2 : rdn source_segs m1 (v_addi sp 228) 4 = Some (lebytes 4 (ir2 i))) by (rewrite <- f_r2; exact (Rd 12%nat 4%nat ltac:(lia))).
  assert (Fo : forall a n v, rdn source_segs m a n = Some v -> bv_unsigned a + Z.of_nat n <= bv_unsigned sp + 216 \/
                bv_unsigned sp + 248 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 -> rdn source_segs m1 a n = Some v).
  { intros a n v H Hd Hb'. rewrite (rd_out _ m m1 (v_addi sp 216) a (encb i) n Km); [exact H | rewrite Us; cbn; lia | lia | rewrite Us; cbn; lia]. }
  assert (F2' : wat m1 (v_addi sp 72) (W 0x50da8)) by (apply Fo; [exact F2 | rewrite Us; cbn; lia | rewrite Us; cbn; lia]).
  assert (F3' : wat m1 (v_addi sp 80) y) by (apply Fo; [exact F3 | rewrite Us; cbn; lia | rewrite Us; cbn; lia]).
  destruct Sy as (Snw & Sr & Sw & Sn).
  destruct (Sr (ir1 i) ltac:(lia)) as (Ok1 & S1a & S1k). destruct (Sr (ir2 i) ltac:(lia)) as (Ok2 & S2a & S2k).
  assert (S1a' := Fo _ _ _ S1a ltac:(rewrite Uy by lia; lia) ltac:(rewrite Uy by lia; cbn; lia)).
  assert (S1k' := Fo _ _ _ S1k ltac:(rewrite Uy by lia; lia) ltac:(rewrite Uy by lia; cbn; lia)).
  assert (S2a' := Fo _ _ _ S2a ltac:(rewrite Uy by lia; lia) ltac:(rewrite Uy by lia; cbn; lia)).
  assert (S2k' := Fo _ _ _ S2k ltac:(rewrite Uy by lia; lia) ltac:(rewrite Uy by lia; cbn; lia)).
  gres. norm_rm.
  lw4 Rk. rewrite lw_small by lia. rewrite Hk.         (* lw s2,216(sp) *)
  st1. st1. st1; kill_closed.                          (* addi ; li ; bltu: kind 9 is in range *)
  lw4 Rr1. rewrite lw_small by lia. st1.               (* lw a1,224(sp) ; slli *)
  lw4 Rr2. rewrite lw_small by lia.                    (* lw a2,228(sp) *)
  ld8 F3'. st1.                                        (* ld a3,80(sp) ; add *)
  (* ld s7,0(a1) ; ld s9,8(a1): r[r1] *)
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_ld_at with (a := v_addi y (16 * ir1 i)); [wxf F | reflexivity | exact D | reflexivity
      | gres; rsub; imm_norm; rewrite sym_addr by lia; f_equal; lia | exact S1a' | apply bytes8] | norm_rm]).
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_ld_at with (a := v_addi y (16 * ir1 i + 8)); [wxf F | reflexivity | exact D | reflexivity
      | gres; rsub; imm_norm; rewrite sym_addr by lia; f_equal; lia | exact S1k' | apply bytes8] | norm_rm]).
  st1. st1. st1.                                       (* slli a2 ; add a2 ; slli a0 *)
  ld8 F2'. st1.                                        (* ld a1,72(sp) ; add *)
  let n := pc_of in fd n ltac:(fun F D => djt F D).    (* lw a0,0(a0): the table entry for kind 9 *)
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_ld_at with (a := v_addi y (16 * ir2 i)); [wxf F | reflexivity | exact D | reflexivity
      | gres; rsub; imm_norm; rewrite sym_addr by lia; f_equal; lia | exact S2a' | apply bytes8] | norm_rm]).
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_ld_at with (a := v_addi y (16 * ir2 i + 8)); [wxf F | reflexivity | exact D | reflexivity
      | gres; rsub; imm_norm; rewrite sym_addr by lia; f_equal; lia | exact S2k' | apply bytes8] | norm_rm]).
  st1.                                                 (* add a0,a0,a1 *)
  let n := pc_of in fd n ltac:(fun F D => djr F D).    (* jr a0 *)
  assert (Out : forall a : word, ~ (bv_unsigned sp + 216 <= bv_unsigned a < bv_unsigned sp + 248) -> m1 a = m a).
  { intros a Ha. rewrite Km. apply wbytes_outside; rewrite Us by lia; cbn; lia. }
  lazymatch goal with |- RunM _ _ _ (mkst _ ?pc _ _) => replace pc with (W 0x3da52) by (apply bv_eq; reflexivity) end.
  apply Kd; gres; rsub; try reflexivity.
  - exact Hc1.
  - exact (writable_meq _ _ _ _ _ _ Km Hwi).
  - exact (writable_meq _ _ _ _ _ _ Km Hwy).
  - apply (frame_same m m1 Fr). intros a _ Ha. apply Out. exact Ha.
  - apply (sym_same m m1 Y (conj Snw (conj Sr (conj Sw Sn)))). intros a Ha. apply Out. lia.
  - rewrite <- f_imm. exact (Rd 16%nat 8%nat ltac:(lia)).
  - rewrite <- f_len. exact (Rd 24%nat 4%nat ltac:(lia)).
Qed.


Lemma Us0 : forall k, 0 <= k < 352 -> bv_unsigned (v_addi sp k) = bv_unsigned sp + k.
Proof. intros; apply u_addi; pose proof (bv_unsigned_in_range _ sp); change (bv_modulus 64) with (2^64) in *; lia. Qed.

Lemma addi2 : forall a b, 0 <= a -> 0 <= b -> a + b < 1032 -> v_addi (v_addi y a) b = v_addi y (a + b).
Proof.
  intros. apply bv_eq. rewrite !u_addi; try lia; rewrite ?Uy0 by lia; pose proof Ly; pose proof (bv_unsigned_in_range _ y);
  change (bv_modulus 64) with (2^64) in *; lia.
Qed.

Lemma add_k_val : forall v k, av_ok v -> avb v <> 0 -> avb v <> 13 ->
  add_k v k = AV (avb v) (ava v) (W64 (avk v + k)).
Proof. intros v k _ H1 H2. unfold add_k, B_UNK, B_TAG. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity. Qed.

Lemma imm_add : forall imm k, 0 <= k < 2 ^ 64 -> v_add (W imm) (W k) = W (W64 (k + imm)).
Proof.
  intros. apply bv_eq. unfold v_add. rewrite !Z_to_bv_unsigned. unfold W64, bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small k) by lia. rewrite Zplus_mod_idemp_l. rewrite Zmod_mod. f_equal. lia.
Qed.

Ltac sdy off :=
  let n := pc_of in fd n ltac:(fun F D =>
    eapply rm_step; [reflexivity | eapply z_sd with (a := v_addi y off); [wxf F | reflexivity | exact D
      | gres; rsub; imm_norm; rewrite ?sym_addr by lia; rewrite ?addi2 by lia; f_equal; lia
      | gres; rsub; reflexivity
      | eapply writable_store_ok with (lo := bv_unsigned y) (hi := bv_unsigned y + 1032);
        [wrt | rewrite Uy0 by lia; lia | rewrite Uy0 by lia; cbn; lia | lia] ] | norm_rm ]).

Ltac rout_any := rewrite rdn_wbytes_out;
  [ | rewrite ?length_word_to_le_bytes; rewrite ?Uy0 by lia; rewrite ?Us0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia
    | rewrite ?Uy0 by lia; rewrite ?Us0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia
    | rewrite ?length_word_to_le_bytes; rewrite ?Uy0 by lia; rewrite ?Us0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia ].

Ltac ldc8 Fw := let n := pc_of in fd n ltac:(fun F D =>
  eapply rm_step; [reflexivity | eapply z_ld_at; [wxf F | reflexivity | exact D | reflexivity
    | gres; rsub; imm_norm; reflexivity | repeat rout_any; exact Fw | apply bytes8] | norm_rm]).
Ltac lwc4 Fw := let n := pc_of in fd n ltac:(fun F D =>
  eapply rm_step; [reflexivity | eapply z_lw_at; [wxf F | reflexivity | exact D | reflexivity
    | gres; rsub; imm_norm; reflexivity | repeat rout_any; exact Fw | apply le4_val; lia] | norm_rm]).

Lemma sd_sym' : forall m Y v1 v2 w1 w2 w3 w4, sym_at m y Y -> ynw Y < 16 -> av_ok v1 -> av_ok v2 ->
  w1 = W (pack v1) -> w2 = W (avk v1) -> w3 = W (pack v2) -> w4 = W (avk v2) ->
  sym_at (wbytes (wbytes (wbytes (wbytes (wbytes m (v_addi y (512 + 32 * ynw Y)) (w8 w1))
    (v_addi y (512 + 32 * ynw Y + 8)) (w8 w2)) (v_addi y 1024) (word_to_le_bytes 4 (W (ynw Y + 1))))
    (v_addi y (512 + 32 * ynw Y + 16)) (w8 w3)) (v_addi y (512 + 32 * ynw Y + 24)) (w8 w4))
    y (Sym (yr Y) (upd (yw Y) (ynw Y) (v1, v2)) (ynw Y + 1)).
Proof. intros. subst. apply sd_sym; assumption. Qed.

Definition sd_next (Y : sym) (i : ins) : sym :=
  Sym (yr Y) (upd (yw Y) (ynw Y) (add_k (yr Y (ir1 i)) (iimm i), yr Y (ir2 i))) (ynw Y + 1).

Lemma add_k_ok : forall v k, av_ok v -> av_ok (add_k v k).
Proof.
  intros v k (H1 & H2 & H3). unfold add_k. destruct (_ || _); cbn; [unfold av_ok; cbn; lia|].
  unfold av_ok; cbn. split; [lia|]. split; [lia|]. unfold W64. apply Z.mod_pos_bound. lia.
Qed.

(** The [sd] case, from 0x3da52 back to the loop head: the store count is checked, the address
    [add_k(a, imm)] and the value [b] are recorded in [w[nw]], [nw] is incremented, and the loop
    moves to the next instruction with one less fuel. *)
Lemma sd_case : forall o fuel Y i regs m Post,
  getr regs 2 = sp -> getr regs 8 = W o -> getr regs 20 = x -> getr regs 26 = W fuel ->
  getr regs 23 = W (pack (yr Y (ir1 i))) -> getr regs 25 = W (avk (yr Y (ir1 i))) ->
  getr regs 27 = W (pack (yr Y (ir2 i))) -> getr regs 24 = W (avk (yr Y (ir2 i))) ->
  0 <= o < 2 ^ 62 -> 2 <= fuel <= 64 -> ins_ok i -> ynw Y < 16 ->
  mem_clear m TL TH -> writable m (bv_unsigned (v_addi sp 216)) (bv_unsigned (v_addi sp 216) + 32) ->
  writable m (bv_unsigned y) (bv_unsigned y + 1032) -> frame_ok m -> sym_at m y Y ->
  rdn source_segs m (v_addi sp 232) 8 = Some (lebytes 8 (iimm i)) ->
  rdn source_segs m (v_addi sp 240) 4 = Some (lebytes 4 (ilen i)) ->
  (forall regs' m', LH (o + ilen i) (fuel - 1) (sd_next Y i) regs' m' -> RunM ra0 rom Post (mkst regs' (W 0x3d7d4) m' rom)) ->
  RunM ra0 rom Post (mkst regs (W 0x3da52) m rom).
Proof.
  intros o fuel Y i regs m Post R2 R8 R20 R26 R23 R25 R27 R24 Ho Hf Hi Hnw Hc Hwi Hwy Fr Sy Rim Rln K.
  pose proof Fr as (F1 & F2 & F3 & F4 & F5 & F6). pose proof Sy as Sy0. destruct Sy0 as (Snw & Sr & Sw & Sn).
  destruct Hi as (Ik & Ird & Ir1 & Ir2 & Il).
  destruct (Sr (ir1 i) ltac:(lia)) as (Oa & _). destruct (Sr (ir2 i) ltac:(lia)) as (Ob & _).
  pose proof (pack_ok _ Oa). pose proof (pack_ok _ Ob). pose proof Oa as (Oa1 & Oa2 & Oa3). pose proof Ob as (Ob1 & Ob2 & Ob3).
  pose proof (bv_unsigned_in_range _ sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  assert (Us : forall k, 0 <= k < 352 -> bv_unsigned (v_addi sp k) = bv_unsigned sp + k) by (intros; apply u_addi; lia).
  norm_rm.
  ld8 F3. lw4 Sn. rewrite lw_small by lia.                 (* ld a0,80(sp) ; lw a0,1024(a0) *)
  st1. st1; kill.                                         (* li a1,16 ; beq a0,a1 *)
  st1. rewrite sextw_pack by exact Oa.                    (* sext.w a3,s7 *)
  st1. st1.                                               (* li a1,0 ; li a2,0 *)
  st1.                                                    (* beqz a3: b = UNK, or not *)
  2: st1. 2: st1.                                        (* li a4,13 ; beq a3,a4: b = TAG, or not *)
  3: ldc8 Rim. 3: st1. 3: st1.                            (* ld a2,232(sp) ; add a2,a2,s9 ; mv a1,s7 *)
  all: st1. all: ld8 F3. all: st1. all: st1.               (* slli a0 ; ld a3,80(sp) ; add ; addi 512 *)
  all: sdy (512 + 32 * ynw Y).                            (* sd a1,0(a0) *)
  all: lwc4 Sn. all: rewrite lw_small by lia.             (* lw a1,1024(a3) *)
  all: sdy (512 + 32 * ynw Y + 8).                        (* sd a2,8(a0) *)
  all: st1.                                               (* addi a0,a1,1 *)
  all: (let n := pc_of in fd n ltac:(fun F D =>            (* sw a0,1024(a3) *)
    eapply rm_step; [reflexivity | eapply z_sw with (a := v_addi y 1024) (v := W (ynw Y + 1)); [wxf F | reflexivity | exact D
      | gres; rsub; imm_norm; reflexivity | gres; rsub; rewrite vW by lia; reflexivity
      | eapply writable_store_ok with (lo := bv_unsigned y) (hi := bv_unsigned y + 1032);
        [wrt | rewrite Uy0 by lia; lia | rewrite Uy0 by lia; cbn; lia | lia] ] | norm_rm ])).
  all: st1. all: st1.                                     (* slli a1 ; add a1 *)
  all: sdy (512 + 32 * ynw Y + 16). all: sdy (512 + 32 * ynw Y + 24).   (* sd s11,528(a1) ; sd s8,536(a1) *)
  all: st1.                                               (* j 3dc02 *)
  all: lwc4 Rln. all: rewrite lw_small by lia.            (* lw s3,240(sp) *)
  all: st1. all: st1. all: ldc8 F1. all: st1; kill.        (* addiw s10 ; add s0 ; ld a4,64(sp) ; bnez s10 *)
  all: lazymatch goal with |- RunM _ _ _ (mkst _ ?pc _ _) => replace pc with (W 0x3d7d4) by (apply bv_eq; reflexivity) end.
  all: apply K.
  all: repeat match goal with H : branch_taken BC_EQ (W (avb _)) _ = _ |- _ =>
         rewrite ?vW in H by lia; rewrite bt_eq in H by lia;
         first [apply Z.eqb_eq in H | apply Z.eqb_neq in H] end.
  all: assert (Hadd : add_k (yr Y (ir1 i)) (iimm i) =
                      if (avb (yr Y (ir1 i)) =? 0) || (avb (yr Y (ir1 i)) =? 13) then UNK
                      else AV (avb (yr Y (ir1 i))) (ava (yr Y (ir1 i))) (W64 (avk (yr Y (ir1 i)) + iimm i))) by reflexivity.
  all: repeat match goal with H : context [Z.add 0 ?c] |- _ => change (Z.add 0 c) with c in H end.
  all: repeat match goal with
         | H : avb _ = ?c |- _ => rewrite H in Hadd; clear H
         | H : avb _ <> ?c |- _ => rewrite (proj2 (Z.eqb_neq _ _) H) in Hadd; clear H
         end; cbn [orb Z.eqb Pos.eqb] in Hadd.
  all: unfold LH, sd_next; rewrite Hadd.
  all: split; [gres; rsub; reflexivity|].
  all: split; [gres; rsub; rewrite vadd_W by lia; reflexivity|].
  all: split; [gres; rsub; reflexivity|].
  all: split; [gres; rsub; reflexivity|].
  all: split; [gres; rsub; rewrite addiw_W by lia; reflexivity|].
  all: split; [lia|]. all: split; [lia|].
  all: split; [clr|].
  all: split; [repeat apply writable_store; exact Hwi|].
  all: split; [repeat apply writable_store; exact Hwy|].
  all: split;
    [ apply (frame_same m _ Fr); intros a Hy Hi;
      repeat (rewrite wbytes_outside; [| rewrite ?length_word_to_le_bytes, ?Uy0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia
                                      | rewrite ?length_word_to_le_bytes, ?Uy0 by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia]);
      reflexivity | ].
  all: apply sd_sym'; [exact Sy | lia | | exact Ob | | | reflexivity | reflexivity].
  all: try (unfold av_ok; cbn; lia).
  all: try (apply bv_eq; reflexivity).
  all: try (unfold UNK, pack; cbn [avb ava avk]; apply bv_eq; reflexivity).
  all: try (rewrite vadd_W by lia; unfold pack; cbn [avb ava]; reflexivity).
  all: try (rewrite imm_add by lia; reflexivity).
  all: try (destruct Oa as (A1 & A2 & A3); unfold av_ok; cbn [avb ava avk]; split; [lia|]; split; [lia|]; unfold W64; apply Z.mod_pos_bound; lia).
Qed.

(** One trip of the loop for an [sd] (rb_iter's I_SD case with room in the log), from the loop head
    back to the loop head: the loop invariant [LH] is preserved with the [Sym] [rb_iter] gives. *)
Theorem sd_iter : forall o fuel Y regs m Post,
  LH o fuel Y regs m -> o <> stop -> o <= stop -> o + 4 <= len -> 2 <= fuel -> o < 2 ^ 62 ->
  let i := cdec (bytes o) (bytes (o + 1)) (bytes (o + 2)) (bytes (o + 3)) in
  ik i = I_SD -> ynw Y < 16 ->
  (forall regs' m' Y', rb_iter E o i Y = INext (o + ilen i) Y' ->
     LH (o + ilen i) (fuel - 1) Y' regs' m' -> RunM ra0 rom Post (mkst regs' (W 0x3d7d4) m' rom)) ->
  RunM ra0 rom Post (mkst regs (W 0x3d7d4) m rom).
Proof.
  intros o fuel Y regs m Post HL Hne Hle Hb Hf Ho i Hk Hn K.
  pose proof HL as (_ & _ & _ & _ & _ & Ho' & Hfu & _).
  apply (dispatch_sd o fuel Y regs m Post HL Hne Hle Hb Hk).
  intros regs' m' R2 R8 R20 R26 R23 R25 R27 R24 Hc Hwi Hwy Fr Sy Rim Rln.
  apply (sd_case o fuel Y i regs' m' Post R2 R8 R20 R26 R23 R25 R27 R24 ltac:(lia) ltac:(lia)
           (Hins _ _ _ _) Hn Hc Hwi Hwy Fr Sy Rim Rln).
  intros regs'' m'' HL'. apply (K regs'' m'' (sd_next Y i)); [|exact HL'].
  unfold rb_iter. rewrite Hk. cbn [Z.eqb Pos.eqb I_LD I_SD].
  rewrite (proj2 (Z.eqb_neq (ynw Y) 16) ltac:(lia)). reflexivity.
Qed.

End Loop.
