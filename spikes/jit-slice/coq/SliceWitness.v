(** * The entry relation is satisfiable, for each of the three outcomes.

    Without this, [slice_refines] could hold only because [Rel] is impossible. *)
From Stdlib Require Import NArith ZArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec MemSplit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Examples.jit_slice Require Import SliceCode SliceBytecode SliceStep SliceProof.
Import ListNotations.
Open Scope bv_scope.

Definition w (z : Z) : word := Z_to_bv 64 z.

Definition wfp : word := w 0x100000.
Definition wvm : word := w 0x200000.
Definition whp : word := w 0x300000.
Definition wpair : word := w 0x400003.
Definition whead : word := w 44.
Definition wret : word := w 0x60000.

Definition wseg : Segment :=
  {| seg_base := 0x5c000; seg_size := 0x1000; seg_perms := "rwx"%string; seg_bytes := [] |}.
Definition wsegs : list Segment := [wseg].

Definition code_mem (a : word) : option byte :=
  let u := bv_unsigned a in
  if (Z.leb code_base u && Z.ltb u (code_base + code_len))%bool
  then Some (code_byte (u - code_base)) else None.

Definition put (m : word -> option byte) (a v : word) := wbytes m a (word_to_le_bytes 8 v).

(** Slots, VM fields, bump room, and one pair's head. *)
Definition wmem (x limit : word) : word -> option byte :=
  let m := code_mem in
  let m := put m wfp wret in
  let m := put m (w 0x100008) (w 0) in
  let m := put m (w 0x100010) x in
  let m := put m (w 0x100018) (w 20) in
  let m := put m (w 0x100020) (w 0) in
  let m := put m (w 0x100028) (w 0) in
  let m := put m wvm (w 0) in
  let m := put m (w 0x200008) limit in
  let m := put m (w 0x200010) (w 0) in
  let m := put m (w 0x200018) (w 0) in
  let m := put m (w 0x200038) (w 0) in
  let m := put m whp (w 0) in
  let m := put m (w 0x300008) (w 0) in
  put m (w 0x400000) whead.

Definition wst (x limit : word) : bstate :=
  mkB (fun k => match k with 0 => wret | 2 => x | 3 => w 20 | _ => w 0 end)%nat
      (fun a => if bool_decide (a = w 0x400000) then Some whead else None)
      whp limit.

Definition wregs (x : word) : bvmap 5 word :=
  regupd (regupd (regupd (regupd (regupd bvmap_empty 8 wfp) 9 wvm) 18 x) 19 whp) 12 (w 2).

Lemma put_miss : forall m a v b,
  (bv_unsigned a + 8 < 2^64)%Z ->
  (bv_unsigned b < bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned b)%Z ->
  put m a v b = m b.
Proof.
  intros m a v b Ha Hb. unfold put.
  apply wbytes_outside; rewrite length_word_to_le_bytes; cbn [Z.of_nat]; lia.
Qed.

Lemma u_w : forall z, (0 <= z)%Z -> (z < 2^64)%Z -> bv_unsigned (w z) = z.
Proof. intros. apply u_Z2bv; lia. Qed.

Lemma wcode : forall x limit, CodeOK wsegs (wmem x limit).
Proof.
  intros x limit. constructor.
  - vm_compute. reflexivity.
  - exists wseg. split; [ | vm_compute; reflexivity ].
    intros a Hl Hh. cbn [wsegs find_segment].
    assert (Hb : code_base = 377152%Z) by reflexivity.
    assert (Hn : code_len = 192%Z) by reflexivity.
    rewrite Hb in Hl. rewrite Hb, Hn in Hh.
    cbn [seg_base seg_size wseg].
    replace (Z.leb (Z.of_N 0x5c000) a && Z.leb (a + 4) (Z.of_N 0x5c000 + Z.of_N 0x1000))%bool with true.
    + reflexivity.
    + symmetry. apply andb_true_intro. split; apply Z.leb_le; cbn [Z.of_N]; lia.
  - intros i Hi. unfold wmem.
    assert (Hb : code_base = 377152%Z) by reflexivity.
    assert (Hn : code_len = 192%Z) by reflexivity.
    assert (Hu : bv_unsigned (at_ i) = (code_base + i)%Z) by (apply u_at; lia).
    rewrite Hb in Hu. rewrite Hn in Hi.
    repeat (rewrite put_miss;
      [ | unfold wfp, wvm, whp; rewrite u_w; lia
        | unfold wfp, wvm, whp; rewrite u_w by lia; lia ]).
    unfold code_mem. rewrite Hu, Hb, Hn.
    replace (Z.leb 377152 (377152 + i) && Z.ltb (377152 + i) (377152 + 192))%bool with true.
    + f_equal. f_equal. lia.
    + symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Ltac zc := vm_compute; first [ reflexivity | discriminate | intros; discriminate ].
Ltac ap := unfold apart; first [ left; zc | right; zc ].

Lemma w_layout : forall x limit, Layout wfp wvm (wst x limit).
Proof.
  intros x limit.
  constructor; cbn [wst bhp bheap].
  all: unfold wfp, wvm, whp; try rewrite !u_w by lia.
  all: try (assert (Hb : code_base = 377152%Z) by reflexivity;
            assert (Hn : code_len = 192%Z) by reflexivity;
            rewrite ?Hb, ?Hn).
  1-9: unfold apart; try lia.
  intros a v Ha.
  destruct (decide (a = w 0x400000)) as [->|N].
  + rewrite u_w by lia. unfold apart. repeat split; lia.
  + rewrite bool_decide_eq_false_2 in Ha by exact N. discriminate.
Time Qed.

Lemma w_heap : forall x limit a v, bheap (wst x limit) a = Some v -> a = w 0x400000 /\ v = whead.
Proof.
  intros x limit a v Ha. cbn [wst bheap] in Ha.
  destruct (decide (a = w 0x400000)) as [E|N].
  - split; [exact E|]. rewrite bool_decide_eq_true_2 in Ha by exact E. injection Ha as <-. reflexivity.
  - rewrite bool_decide_eq_false_2 in Ha by exact N. discriminate.
Time Qed.

(** Compare read results as numbers: [decide] on bit vectors builds large proof terms in
    the kernel's VM, which ran this file out of memory. *)
Definition zs (o : option (list byte)) : option (list Z) :=
  match o with Some l => Some (map (fun b : byte => bv_unsigned b) l) | None => None end.

Lemma zs_inj : forall o1 o2, zs o1 = zs o2 -> o1 = o2.
Proof.
  intros [l1|] [l2|] H; try discriminate; [ | reflexivity ].
  cbn in H. injection H as H. f_equal. revert l2 H.
  induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate; [ reflexivity | ].
  cbn in H. injection H as Hab H. f_equal; [ apply bv_eq; exact Hab | apply IH; exact H ].
Qed.

Ltac rd := apply zs_inj; vm_compute; reflexivity.

Lemma w_mem : forall x limit,
  x = wpair \/ x = w 8 -> limit = w 0x400000 \/ limit = w 0x300008 ->
  MemRel wsegs wfp wvm 6 (wst x limit) (wmem x limit).
Proof.
  intros x limit Hx Hl.
  destruct Hx as [Hx|Hx]; destruct Hl as [Hl|Hl]; subst x limit; constructor.
  all: try (intros k Hk; do 6 (destruct k as [|k]; [ rd | ]); lia).
  all: try rd.
  all: intros a v Ha; destruct (w_heap _ _ a v Ha) as [-> ->]; rd.
Time Qed.

Lemma w_write : forall x limit,
  x = wpair \/ x = w 8 -> limit = w 0x400000 \/ limit = w 0x300008 ->
  Writable wsegs wfp wvm (wst x limit) (wmem x limit).
Proof.
  intros x limit Hx Hl.
  destruct Hx as [Hx|Hx]; destruct Hl as [Hl|Hl]; subst x limit; constructor; vm_compute; reflexivity.
Time Qed.

Lemma w_rel : forall x limit,
  x = wpair \/ x = w 8 ->
  limit = w 0x400000 \/ limit = w 0x300008 ->
  Rel wsegs wfp wvm (wst x limit) (wregs x) (wmem x limit).
Proof.
  intros x limit Hx Hl. constructor.
  - unfold wregs. repeat (rewrite getr_other by reg_neq_tac). rewrite getr_same by reg_neq_tac. reflexivity.
  - unfold wregs. repeat (rewrite getr_other by reg_neq_tac). rewrite getr_same by reg_neq_tac. reflexivity.
  - unfold wregs. repeat (rewrite getr_other by reg_neq_tac). rewrite getr_same by reg_neq_tac. reflexivity.
  - unfold wregs. repeat (rewrite getr_other by reg_neq_tac). rewrite getr_same by reg_neq_tac. reflexivity.
  - unfold wregs. rewrite getr_same by reg_neq_tac. reflexivity.
  - apply w_layout.
  - apply w_mem; assumption.
  - apply w_write; assumption.
  - apply wcode.
  - destruct Hx as [Hx|Hx]; subst x; cbn [wst bslots]; intros Ht.
    + exists whead. unfold vadd. cbn [wst bheap].
      rewrite bool_decide_eq_true_2. { reflexivity. } apply bv_eq. vm_compute. reflexivity.
    + vm_compute in Ht. discriminate.
Time Qed.

Definition is_return (r : bresult) := match r with BReturn _ _ => true | _ => false end.
Definition is_raise (r : bresult) := match r with BRaise _ _ _ => true | _ => false end.
Definition is_collect (r : bresult) := match r with BCollect _ _ => true | _ => false end.

(** One related state for each outcome of [slice_refines]. *)
Theorem witness_return : is_return (brun slice_prog (wst wpair (w 0x400000))) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem witness_collect : is_collect (brun slice_prog (wst wpair (w 0x300008))) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem witness_raise : is_raise (brun slice_prog (wst (w 8) (w 0x400000))) = true.
Proof. vm_compute. reflexivity. Qed.

