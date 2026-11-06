(** * Rung 4 (restricted): for a heap of pairs and non-pointers only, the memory the
    scan leaves is isomorphic to the graph it started from.

    This is about the relations of rungs 2 and 3, which the machine provably follows.  It
    covers no header-carrying object, no large object, and no symbol or code sweep.  The
    root loop in [collect_into] isn't proved on the binary: roots appear here as the fact
    that their cells are already forwarded when the scan starts. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Run.
From LinuxProcessSemantics.Common Require Import PropExec CatExec CatSim SeqExec StepTac WxExec StoreOk.
From LinuxProcessSemantics.Examples.gc_rate_ns Require Import gc_rate_code GcStep GcTac GcMem Rung1ObjWords Rung2Frame Rung2Paths Rung2Pointer Rung2ObjSize Rung2Spine Rung3Scan.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.
Set Default Timeout 60.

Lemma w_dec : forall x p : word, {x = p} + {x <> p}.
Proof.
  intros x p. destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned p)) as [H|H].
  - left. apply bv_eq. exact H.
  - right. intro E. apply H. rewrite E. reflexivity.
Qed.

Lemma wat_fun : forall m (a x y : word), wat m a x -> wat m a y -> x = y.
Proof.
  intros m a x y Hx Hy. unfold wat in *. rewrite Hx in Hy.
  pose proof (f_equal (fun o => match o with Some l => bytes_le_to_Z l | None => 0 end) Hy) as H.
  cbv beta iota in H. rewrite !bytes8 in H. apply bv_eq. exact H.
Qed.

Section Graph.
Context {fx : FPState}.

Variables (c from fw q0 tohi sp s1v : word).
Let fp : word := at_off sp (-48).
Let fromhi : Z := bv_unsigned from + 8 * bv_unsigned fw.
Hypothesis Hfl : TH <= bv_unsigned from.
Hypothesis Htl : TH <= bv_unsigned q0 <= bv_unsigned tohi.
Hypothesis Hdis : bv_unsigned tohi <= bv_unsigned from \/ fromhi <= bv_unsigned q0.
Hypothesis Hfs : fromhi <= bv_unsigned fp.
Hypothesis Hsp8 : TH <= bv_unsigned fp.
Hypothesis Hts : bv_unsigned tohi <= bv_unsigned fp.
Hypothesis Hfc : bv_unsigned fp + 48 <= bv_unsigned c.
Hypothesis Hch : bv_unsigned c + 56 <= 2^63.

(** The graph: pair cells with their two original values.  Every value is a non-pointer
    or a pair-tagged pointer to another cell; cells don't overlap and sit in from-space. *)
Variables (cell : word -> Prop) (o0 o1 : word -> word).

Definition val_ok (v : word) : Prop :=
  non_ptr_tag (tag v) \/ (tag v = 3 /\ cell (ptr_of v)).

Hypothesis cell_from : forall p, cell p ->
  bv_unsigned from <= bv_unsigned p /\ bv_unsigned p + 16 <= fromhi.
Hypothesis cell_disj : forall p p', cell p -> cell p' -> p <> p' ->
  bv_unsigned p + 16 <= bv_unsigned p' \/ bv_unsigned p' + 16 <= bv_unsigned p.
Hypothesis cell_vals : forall p, cell p -> val_ok (o0 p) /\ val_ok (o1 p).
Hypothesis cell_head : forall p, cell p -> o0 p <> V_FORWARD.

(** The forwarding map, as a partial function. *)
Definition img (phi : word -> option word) (v : word) : word :=
  if (tag v =? 3) then
    match phi (ptr_of v) with Some q => pair_moved q | None => v end
  else v.

(** What the word at [x] holds, with the scan at [a]: its image if already scanned. *)
Definition show (phi : word -> option word) (a x w : word) : word :=
  if (bv_unsigned x <? bv_unsigned a) then img phi w else w.

Definition done (phi : word -> option word) (a x w : word) : Prop :=
  bv_unsigned x < bv_unsigned a -> tag w = 3 -> exists q, phi (ptr_of w) = Some q.

(** Addresses of to-space cells, aligned on 16-byte steps from the start. *)
Definition to_cell (q : word) : Prop :=
  bv_unsigned q0 <= bv_unsigned q /\ (bv_unsigned q - bv_unsigned q0) mod 16 = 0.

(** THE INVARIANT.  [a] is the scan position in bytes, [nx] the copy cursor. *)
Record Inv (phi : word -> option word) (m : word -> option byte) (a nx : word) : Prop := {
  i_next : wat m (at_off c 16) nx;
  i_nx : to_cell nx /\ bv_unsigned nx <= bv_unsigned tohi;
  i_a : bv_unsigned q0 <= bv_unsigned a <= bv_unsigned nx;
  i_uncopied : forall p, cell p -> phi p = None ->
     wat m p (o0 p) /\ wat m (at_off p 8) (o1 p);
  i_copied : forall p q, phi p = Some q ->
     cell p /\ wat m p V_FORWARD /\ wat m (at_off p 8) (pair_moved q) /\
     to_cell q /\ bv_unsigned q + 16 <= bv_unsigned nx /\
     wat m q (show phi a q (o0 p)) /\ wat m (at_off q 8) (show phi a (at_off q 8) (o1 p)) /\
     done phi a q (o0 p) /\ done phi a (at_off q 8) (o1 p);
  i_inj : forall p p' q, phi p = Some q -> phi p' = Some q -> p = p';
  i_surj : forall q, to_cell q -> bv_unsigned q < bv_unsigned nx -> exists p, phi p = Some q
}.

Definition extends (phi phi' : word -> option word) : Prop :=
  forall p q, phi p = Some q -> phi' p = Some q.

Lemma extends_refl : forall phi, extends phi phi.
Proof. intros phi p q H. exact H. Qed.

Lemma extends_trans : forall a b d, extends a b -> extends b d -> extends a d.
Proof. intros a b d H1 H2 p q H. apply H2, H1, H. Qed.

Lemma img_stable : forall phi phi' v,
  extends phi phi' -> (tag v = 3 -> exists q, phi (ptr_of v) = Some q) -> img phi' v = img phi v.
Proof.
  intros phi phi' v Hx Hd. unfold img.
  destruct (Z.eqb_spec (tag v) 3) as [E|E]; [|reflexivity].
  destruct (Hd E) as (q & Hq). rewrite Hq, (Hx _ _ Hq). reflexivity.
Qed.

Lemma show_stable : forall phi phi' a x w,
  extends phi phi' -> done phi a x w -> show phi' a x w = show phi a x w.
Proof.
  intros phi phi' a x w Hx Hd. unfold show.
  destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a)) as [L|L]; [|reflexivity].
  apply img_stable; [exact Hx|]. intro E. exact (Hd L E).
Qed.

Lemma done_stable : forall phi phi' a x w,
  extends phi phi' -> done phi a x w -> done phi' a x w.
Proof.
  intros phi phi' a x w Hx Hd L E. destruct (Hd L E) as (q & Hq). exists q. apply Hx, Hq.
Qed.

(** [m'] keeps every word disjoint from [xs]. *)
Definition keeps (m m' : word -> option byte) (xs : list word) : Prop :=
  forall (a v : word), wat m a v -> bv_unsigned a + 8 <= 2^63 ->
    Forall (fun x => bv_unsigned x + 8 <= bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned x) xs ->
    wat m' a v.

Definition fupd (phi : word -> option word) (p q : word) : word -> option word :=
  fun x => if bv_eqb x p then Some q else phi x.

Lemma bv_eqb_true : forall x p : word, x = p -> bv_eqb x p = true.
Proof. intros x p ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma bv_eqb_false : forall x p : word, x <> p -> bv_eqb x p = false.
Proof.
  intros x p Hn. unfold bv_eqb. apply Z.eqb_neq. intro He. apply Hn. apply bv_eq. exact He.
Qed.

Lemma fupd_extends : forall phi p q, phi p = None -> extends phi (fupd phi p q).
Proof.
  intros phi p q Hn x y Hxy. unfold fupd.
  destruct (w_dec x p) as [->|Hne]; [rewrite Hn in Hxy; discriminate|].
  rewrite bv_eqb_false by exact Hne. exact Hxy.
Qed.

Lemma word_range : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. exact (bv_unsigned_in_range _ x). Qed.

Definition cover (q : word) : Prop := bv_unsigned q + 16 <= bv_unsigned tohi.

Lemma to_add16 : forall q : word, to_cell q -> bv_unsigned q + 16 < 2^64 -> to_cell (at_off q 16).
Proof.
  intros q [H1 H2] Hb. pose proof (word_range q). unfold to_cell.
  rewrite u_at_off by lia. split; [lia|].
  replace (bv_unsigned q + 16 - bv_unsigned q0) with ((bv_unsigned q - bv_unsigned q0) + 1 * 16) by lia.
  rewrite Z.mod_add by lia. exact H2.
Qed.

Lemma aligned_next : forall q nx : word, to_cell q -> to_cell nx -> bv_unsigned q < bv_unsigned nx + 16 ->
  q = nx \/ bv_unsigned q + 16 <= bv_unsigned nx.
Proof.
  intros q nx [A1 A2] [B1 B2] Hl.
  destruct (w_dec q nx) as [E|Hn]; [left; exact E|right].
  assert (Hu : bv_unsigned q <> bv_unsigned nx) by (intro E; apply Hn, bv_eq, E).
  pose proof (Z_div_mod_eq_full (bv_unsigned q - bv_unsigned q0) 16) as Da.
  pose proof (Z_div_mod_eq_full (bv_unsigned nx - bv_unsigned q0) 16) as Db.
  rewrite A2 in Da. rewrite B2 in Db. lia.
Qed.

(** THE COPY STEP: forwarding one more cell keeps the invariant. *)
Lemma inv_copy : forall phi m m' a nx p,
  Inv phi m a nx -> cell p -> phi p = None -> cover nx ->
  keeps m m' [nx; at_off nx 8; p; at_off p 8; at_off c 16] ->
  wat m' nx (o0 p) -> wat m' (at_off nx 8) (o1 p) ->
  wat m' p V_FORWARD -> wat m' (at_off p 8) (pair_moved nx) ->
  wat m' (at_off c 16) (at_off nx 16) ->
  Inv (fupd phi p nx) m' a (at_off nx 16).
Proof.
  intros phi m m' a nx p [Inx [Tn Tb] [Ia1 Ia2] Iu Ico Iin Isu] Hcp Hn Hcov Hk W0 W1 W2 W3 W4.
  unfold cover in Hcov. pose proof Tn as [Tn1 _].
  pose proof (word_range nx) as Rn. pose proof (word_range p) as Rp.
  pose proof (word_range fp) as Rf. pose proof (word_range c) as Rc.
  pose proof (cell_from p Hcp) as [Cp1 Cp2].
  assert (Hx := fupd_extends phi p nx Hn).
  assert (Unx8 : bv_unsigned (at_off nx 8) = bv_unsigned nx + 8) by (apply u_at_off; lia).
  assert (Unx16 : bv_unsigned (at_off nx 16) = bv_unsigned nx + 16) by (apply u_at_off; lia).
  assert (Up8 : bv_unsigned (at_off p 8) = bv_unsigned p + 8) by (apply u_at_off; lia).
  assert (Uc : bv_unsigned (at_off c 16) = bv_unsigned c + 16) by (apply u_at_off; lia).
  assert (Dfrom : forall z : word, bv_unsigned from <= bv_unsigned z -> bv_unsigned z + 8 <= fromhi ->
     z <> p -> z <> at_off p 8 ->
     (forall w, cell w -> w = p -> True) ->
     (bv_unsigned z + 8 <= bv_unsigned p \/ bv_unsigned p + 16 <= bv_unsigned z) ->
     Forall (fun x => bv_unsigned x + 8 <= bv_unsigned z \/ bv_unsigned z + 8 <= bv_unsigned x)
       [nx; at_off nx 8; p; at_off p 8; at_off c 16]).
  { intros z Z1 Z2 _ _ _ Zd. unfold fromhi in *.
    repeat (apply Forall_cons; [rewrite ?Unx8, ?Up8, ?Uc; lia|]); apply Forall_nil. }
  assert (Dto : forall z : word, bv_unsigned q0 <= bv_unsigned z -> bv_unsigned z + 8 <= bv_unsigned nx ->
     Forall (fun x => bv_unsigned x + 8 <= bv_unsigned z \/ bv_unsigned z + 8 <= bv_unsigned x)
       [nx; at_off nx 8; p; at_off p 8; at_off c 16]).
  { intros z Z1 Z2. unfold fromhi in *.
    repeat (apply Forall_cons; [rewrite ?Unx8, ?Up8, ?Uc; lia|]); apply Forall_nil. }
  constructor.
  - exact W4.
  - split; [apply to_add16; [exact Tn|lia]|rewrite Unx16; lia].
  - rewrite Unx16. lia.
  - intros p' Hc' Hn'.
    assert (Hne : p' <> p).
    { intro E. subst p'. unfold fupd in Hn'. rewrite bv_eqb_true in Hn' by reflexivity. discriminate. }
    unfold fupd in Hn'. rewrite bv_eqb_false in Hn' by exact Hne.
    destruct (Iu p' Hc' Hn') as [U0 U1].
    pose proof (cell_from p' Hc') as [C1 C2]. pose proof (word_range p') as Rq.
    assert (Up' : bv_unsigned (at_off p' 8) = bv_unsigned p' + 8) by (apply u_at_off; lia).
    pose proof (cell_disj p p' Hcp Hc' (fun E => Hne (eq_sym E))) as Dp.
    split.
    + eapply Hk; [exact U0|unfold fromhi in *; lia|].
      apply Dfrom; try lia; try (intros; exact I).
      * exact Hne.
      * intro E. rewrite E, Up8 in *. lia.
    + eapply Hk; [exact U1|rewrite Up'; unfold fromhi in *; lia|].
      apply Dfrom; rewrite ?Up'; try lia; try (intros; exact I).
      * intro E. rewrite E in Up'. lia.
      * intro E. rewrite E, Up8 in Up'. lia.
  - intros x q Hxq. unfold fupd in Hxq.
    destruct (w_dec x p) as [->|Hne].
    + rewrite bv_eqb_true in Hxq by reflexivity. injection Hxq as <-.
      assert (S0 : show (fupd phi p nx) a nx (o0 p) = o0 p).
      { unfold show. rewrite (proj2 (Z.ltb_ge _ _) Ia2). reflexivity. }
      assert (Hle : bv_unsigned a <= bv_unsigned (at_off nx 8)) by (rewrite Unx8; lia).
      assert (S1 : show (fupd phi p nx) a (at_off nx 8) (o1 p) = o1 p).
      { unfold show. rewrite (proj2 (Z.ltb_ge _ _) Hle). reflexivity. }
      split; [exact Hcp|]. split; [exact W2|]. split; [exact W3|]. split; [exact Tn|].
      split; [rewrite Unx16 |]. { lia. } 
      rewrite S0, S1. split; [exact W0|]. split; [exact W1|].
      split; intros L; lia.
    + rewrite bv_eqb_false in Hxq by exact Hne.
      destruct (Ico x q Hxq) as (Cx & F0 & F1 & Tq & Bq & V0 & V1 & Do0 & Do1).
      pose proof (cell_from x Cx) as [C1 C2]. pose proof (word_range x) as Rq. pose proof (word_range q) as Rqq.
      assert (Ux : bv_unsigned (at_off x 8) = bv_unsigned x + 8) by (apply u_at_off; lia).
      assert (Uq : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
      pose proof (cell_disj p x Hcp Cx (fun E => Hne (eq_sym E))) as Dp.
      destruct Tq as [Tq1 Tq2].
      split; [exact Cx|].
      split.
      { eapply Hk; [exact F0|unfold fromhi in *; lia|].
        apply Dfrom; try lia; try (intros; exact I).
        - exact Hne.
        - intro E. rewrite E, Up8 in *. lia. }
      split.
      { eapply Hk; [exact F1|rewrite Ux; unfold fromhi in *; lia|].
        apply Dfrom; rewrite ?Ux; try lia; try (intros; exact I).
        - intro E. rewrite E in Ux. lia.
        - intro E. rewrite E, Up8 in Ux. lia. }
      split; [split; assumption|].
      split; [rewrite Unx16; lia|].
      rewrite (show_stable phi _ a q _ Hx Do0), (show_stable phi _ a _ _ Hx Do1).
      split.
      { eapply Hk; [exact V0|lia|]. apply Dto; lia. }
      split.
      { eapply Hk; [exact V1|rewrite Uq; lia|]. apply Dto; rewrite Uq; lia. }
      split; eapply done_stable; eassumption.
  - intros x x' q Hx1 Hx2. unfold fupd in Hx1, Hx2.
    destruct (w_dec x p) as [->|N1]; destruct (w_dec x' p) as [->|N2]; try reflexivity.
    + rewrite bv_eqb_true in Hx1 by reflexivity. rewrite bv_eqb_false in Hx2 by exact N2.
      injection Hx1 as <-. destruct (Ico x' nx Hx2) as (_ & _ & _ & _ & Bq & _). lia.
    + rewrite bv_eqb_true in Hx2 by reflexivity. rewrite bv_eqb_false in Hx1 by exact N1.
      injection Hx2 as <-. destruct (Ico x nx Hx1) as (_ & _ & _ & _ & Bq & _). lia.
    + rewrite bv_eqb_false in Hx1 by exact N1. rewrite bv_eqb_false in Hx2 by exact N2.
      eapply Iin; eassumption.
  - intros q Tq Lq. rewrite Unx16 in Lq.
    destruct (aligned_next q nx Tq Tn Lq) as [->|Lt].
    + exists p. unfold fupd. rewrite bv_eqb_true by reflexivity. reflexivity.
    + destruct (Isu q Tq ltac:(lia)) as (x & Hxq). exists x. apply Hx, Hxq.
Qed.

Lemma write_keep : forall m (x y a v : word),
  wat m a v -> bv_unsigned a + 8 <= 2^63 -> bv_unsigned x + 8 <= 2^63 ->
  (bv_unsigned x + 8 <= bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned x) ->
  wat (wbytes m x (w8 y)) a v.
Proof.
  intros m x y a v Hw Ha Hx Hd. apply wat_other; [exact Hw|lia|lia|lia].
Qed.

Lemma forall5 : forall (P : word -> Prop) (a b d e f : word),
  Forall P [a; b; d; e; f] -> P a /\ P b /\ P d /\ P e /\ P f.
Proof.
  intros P a b d e f H.
  inversion H as [|? ? P1 T1]; subst. inversion T1 as [|? ? P2 T2]; subst.
  inversion T2 as [|? ? P3 T3]; subst. inversion T3 as [|? ? P4 T4]; subst.
  inversion T4 as [|? ? P5 _]; subst. repeat split; assumption.
Qed.

Lemma v_ori_moved : forall cur : word, v_ori cur 3 = pair_moved cur.
Proof.
  intros cur. unfold v_ori, pair_moved, v_or.
  change (bv_wrap 64 3) with 3. change (bv_unsigned (Z_to_bv 64 3)) with 3.
  rewrite Z.lor_comm. reflexivity.
Qed.

(** Facts about the two write sequences that copy a cell. *)
Definition slots_ok (q p : word) : Prop :=
  bv_unsigned from <= bv_unsigned p /\ bv_unsigned p + 16 <= fromhi /\
  bv_unsigned q0 <= bv_unsigned q /\ bv_unsigned q + 16 <= bv_unsigned tohi.

Lemma pair_write_ok : forall m q p w0 w1 mv,
  slots_ok q p ->
  let m' := pair_write c m q p w0 w1 mv in
  keeps m m' [q; at_off q 8; p; at_off p 8; at_off c 16] /\
  wat m' q w0 /\ wat m' (at_off q 8) w1 /\ wat m' p V_FORWARD /\ wat m' (at_off p 8) mv /\
  wat m' (at_off c 16) (at_off q 16).
Proof.
  intros m q p w0 w1 mv [H1 [H2 [H3 H4]]]. cbv zeta.
  pose proof (word_range q) as Rq. pose proof (word_range p) as Rp. pose proof (word_range c) as Rc.
  pose proof (word_range fp) as Rf.
  assert (Uq : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
  assert (Up : bv_unsigned (at_off p 8) = bv_unsigned p + 8) by (apply u_at_off; lia).
  assert (Uc : bv_unsigned (at_off c 16) = bv_unsigned c + 16) by (apply u_at_off; lia).
  unfold fromhi in *.
  unfold pair_write. split; [|split; [|split; [|split; [|split]]]].
  - intros a v Hw Ha Hf. apply forall5 in Hf. destruct Hf as (F1 & F2 & F3 & F4 & F5).
    rewrite ?Uq, ?Up, ?Uc in *.
    repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]). exact Hw.
  - repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]).
    apply wat_hit. lia.
  - repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]).
    apply wat_hit. rewrite Uq. lia.
  - apply write_keep; rewrite ?Up; [|lia|lia|lia]. apply wat_hit. lia.
  - apply wat_hit. rewrite Up. lia.
  - repeat (apply write_keep; rewrite ?Up, ?Uc; [|lia|lia|lia]).
    apply wat_hit. rewrite Uc. lia.
Qed.

Lemma spine_write_ok : forall m q p w0 w1,
  slots_ok q p ->
  let m' := spine_write c m q p w0 w1 in
  keeps m m' [q; at_off q 8; p; at_off p 8; at_off c 16] /\
  wat m' q w0 /\ wat m' (at_off q 8) w1 /\ wat m' p V_FORWARD /\ wat m' (at_off p 8) (pair_moved q) /\
  wat m' (at_off c 16) (at_off q 16).
Proof.
  intros m q p w0 w1 [H1 [H2 [H3 H4]]]. cbv zeta.
  pose proof (word_range q) as Rq. pose proof (word_range p) as Rp. pose proof (word_range c) as Rc.
  pose proof (word_range fp) as Rf.
  assert (Uq : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
  assert (Up : bv_unsigned (at_off p 8) = bv_unsigned p + 8) by (apply u_at_off; lia).
  assert (Uc : bv_unsigned (at_off c 16) = bv_unsigned c + 16) by (apply u_at_off; lia).
  unfold fromhi in *.
  unfold spine_write. cbv zeta. rewrite v_ori_moved. split; [|split; [|split; [|split; [|]]]].
  - intros a v Hw Ha Hf. apply forall5 in Hf. destruct Hf as (F1 & F2 & F3 & F4 & F5).
    rewrite ?Uq, ?Up, ?Uc in *.
    repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]). exact Hw.
  - repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]).
    apply wat_hit. lia.
  - repeat (apply write_keep; rewrite ?Uq, ?Up, ?Uc; [|lia|lia|lia]).
    apply wat_hit. rewrite Uq. lia.
  - apply write_keep; rewrite ?Uc; [|lia|lia|lia].
    apply write_keep; rewrite ?Up; [|lia|lia|lia]. apply wat_hit. lia.
  - split.
    + apply write_keep; rewrite ?Uc, ?Up; [|lia|lia|lia]. apply wat_hit. rewrite Up. lia.
    + apply wat_hit. rewrite Uc. lia.
Qed.

(** Words the invariant mentions all lie outside the call frame. *)
Definition inv_addr (z : word) : Prop :=
  bv_unsigned z + 8 <= bv_unsigned fp \/ z = at_off c 16.

Lemma inv_mono : forall phi m m' a nx,
  Inv phi m a nx ->
  (forall z v, wat m z v -> inv_addr z -> wat m' z v) ->
  Inv phi m' a nx.
Proof.
  intros phi m m' a nx [I1 I2 I3 I4 I5 I6 I7] Hk.
  pose proof I2 as [_ Tb].
  constructor; try assumption.
  - apply Hk; [exact I1|right; reflexivity].
  - intros p Hc Hn. destruct (I4 p Hc Hn) as [U0 U1]. pose proof (cell_from p Hc) as [C1 C2].
    pose proof (word_range p) as Rp.
    assert (Up : bv_unsigned (at_off p 8) = bv_unsigned p + 8) by (apply u_at_off; unfold fromhi in *; pose proof (word_range fp); lia).
    split; (apply Hk; [assumption|left; rewrite ?Up; unfold fromhi in *; lia]).
  - intros p q Hp. destruct (I5 p q Hp) as (Cx & F0 & F1 & Tq & Bq & V0 & V1 & D0 & D1).
    pose proof (cell_from p Cx) as [C1 C2]. pose proof (word_range p) as Rp. pose proof (word_range q) as Rq.
    pose proof (word_range fp) as Rf.
    assert (Up : bv_unsigned (at_off p 8) = bv_unsigned p + 8) by (apply u_at_off; unfold fromhi in *; lia).
    assert (Uq : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
    split; [exact Cx|]. split; [apply Hk; [exact F0|left; unfold fromhi in *; lia]|].
    split; [apply Hk; [exact F1|left; rewrite Up; unfold fromhi in *; lia]|].
    split; [exact Tq|]. split; [exact Bq|].
    split; [apply Hk; [exact V0|left; lia]|].
    split; [apply Hk; [exact V1|left; rewrite Uq; lia]|].
    split; assumption.
Qed.

(** Copying a cell, given what [wat] says at the cell. *)
Lemma copy_cell : forall phi m a nx p w0 w1 m',
  Inv phi m a nx -> cell p ->
  wat m p w0 -> w0 <> V_FORWARD -> wat m (at_off p 8) w1 ->
  bv_unsigned nx + 16 <= bv_unsigned tohi ->
  keeps m m' [nx; at_off nx 8; p; at_off p 8; at_off c 16] ->
  wat m' nx w0 -> wat m' (at_off nx 8) w1 -> wat m' p V_FORWARD ->
  wat m' (at_off p 8) (pair_moved nx) -> wat m' (at_off c 16) (at_off nx 16) ->
  phi p = None /\ w0 = o0 p /\ w1 = o1 p /\ Inv (fupd phi p nx) m' a (at_off nx 16).
Proof.
  intros phi m a nx p w0 w1 m' I Hc H0 Hne H1 Hb Hk W0 W1 W2 W3 W4.
  assert (Hn : phi p = None).
  { destruct (phi p) as [q|] eqn:E; [|reflexivity].
    destruct (i_copied _ _ _ _ I p q E) as (_ & F0 & _). exfalso. apply Hne. exact (wat_fun _ _ _ _ H0 F0). }
  destruct (i_uncopied _ _ _ _ I p Hc Hn) as [U0 U1].
  assert (E0 : w0 = o0 p) by exact (wat_fun _ _ _ _ H0 U0).
  assert (E1 : w1 = o1 p) by exact (wat_fun _ _ _ _ H1 U1).
  subst w0 w1.
  split; [exact Hn|]. split; [reflexivity|]. split; [reflexivity|].
  eapply inv_copy; try exact I; try exact Hc; try exact Hn; try exact Hb; try exact Hk;
    assumption.
Qed.

(** The spine loop keeps the invariant. *)
Lemma inv_spine : forall m cur t m' cur',
  spine c from fw q0 tohi m cur t m' cur' ->
  forall phi a, Inv phi m a cur -> tag t = 3 -> cell (ptr_of t) ->
  exists phi', extends phi phi' /\ Inv phi' m' a cur'.
Proof.
  induction 1; intros phi a I Ht Hc.
  - exists phi. split; [apply extends_refl|exact I].
  - exists phi. split; [apply extends_refl|exact I].
  - exists phi. split; [apply extends_refl|exact I].
  - pose proof (cell_from _ Hc) as [C1 C2].
    assert (Hs : slots_ok cur (ptr_of t)) by (repeat split; assumption).
    destruct (spine_write_ok m cur (ptr_of t) w0 w1 Hs) as (Hk & W0 & W1 & W2 & W3 & W4).
    destruct (copy_cell phi m a cur (ptr_of t) w0 w1 _ I Hc H1 H2 H3 H5 Hk W0 W1 W2 W3 W4) as (Hn & _ & _ & I2).
    eexists. split; [apply fupd_extends; exact Hn|exact I2].
  - pose proof (cell_from _ Hc) as [C1 C2].
    assert (Hs : slots_ok cur (ptr_of t)) by (repeat split; assumption).
    destruct (spine_write_ok m cur (ptr_of t) w0 w1 Hs) as (Hk & W0 & W1 & W2 & W3 & W4).
    destruct (copy_cell phi m a cur (ptr_of t) w0 w1 _ I Hc H1 H2 H3 H5 Hk W0 W1 W2 W3 W4) as (Hn & _ & E1 & I2).
    destruct (proj2 (cell_vals _ Hc)) as [Hnp|[_ Cn]].
    + exfalso. rewrite <- E1 in Hnp. rewrite H6 in Hnp. destruct Hnp as [E|[E|[E|E]]]; lia.
    + rewrite <- E1 in Cn.
      destruct (IHspine _ _ I2 H6 Cn) as (phi' & Hx & I3).
      exists phi'. split; [eapply extends_trans; [apply fupd_extends; exact Hn|exact Hx]|exact I3].
Qed.

Lemma wat_push_inv : forall m ra s0 s1 s2 s3 z v,
  wat m z v -> inv_addr z -> wat (M fp ra s0 s1 s2 s3 m) z v.
Proof.
  intros m ra s0 s1 s2 s3 z v Hw Hz. pose proof (word_range fp) as Rf. pose proof (word_range c) as Rc.
  assert (Uc : bv_unsigned (at_off c 16) = bv_unsigned c + 16) by (apply u_at_off; lia).
  unfold M. apply wat_push; [exact Hw|lia| |].
  - destruct Hz as [Hz| ->]; [left; lia|right; rewrite Uc; lia].
  - destruct Hz as [Hz| ->]; [lia|rewrite Uc; lia].
Qed.

(** One [copy_value] call on a pointer to a cell. *)
Lemma inv_call : forall ra s0 s1 s2 s3 phi m a nx v m0 res,
  Inv phi m a nx -> tag v = 3 -> cell (ptr_of v) ->
  cv_rel c from fw q0 tohi fp ra s0 s1 s2 s3 m v m0 res ->
  exists phi' nx', extends phi phi' /\ Inv phi' m0 a nx' /\ res = img phi' v /\
    (exists q, phi' (ptr_of v) = Some q).
Proof.
  intros ra s0 s1 s2 s3 phi m a nx v m0 res I Ht Hc Hr.
  assert (IM : Inv phi (M fp ra s0 s1 s2 s3 m) a nx).
  { eapply inv_mono; [exact I|]. intros z y Hw Hz. apply wat_push_inv; assumption. }
  destruct Hr.
  - exfalso. rewrite Ht in H. destruct H as [E|[E|[E|E]]]; lia.
  - destruct (phi (ptr_of v)) as [q|] eqn:E.
    + destruct (i_copied _ _ _ _ I _ q E) as (_ & _ & F1 & _).
      assert (Ef : fwd = pair_moved q) by exact (wat_fun _ _ _ _ H3 F1).
      exists phi, nx. split; [apply extends_refl|]. split; [exact IM|].
      split; [unfold img; rewrite Ht, E; simpl; exact Ef|exists q; exact E].
    + exfalso. destruct (i_uncopied _ _ _ _ I _ Hc E) as [U0 _].
      apply (cell_head _ Hc). exact (wat_fun _ _ _ _ U0 H2).
  - destruct H0 as [H0a _].
    assert (Eq : q = nx) by (eapply wat_fun; [exact H5|exact (i_next _ _ _ _ I)]).
    subst q.
    pose proof (cell_from _ Hc) as [C1 C2].
    assert (Hs : slots_ok nx (ptr_of v)) by (repeat split; assumption).
    set (Mm := M fp ra s0 s1 s2 s3 m) in *.
    assert (W00 : wat Mm (ptr_of v) w0) by (apply wat_push_inv; [assumption|left; unfold fromhi in *; pose proof (word_range fp); lia]).
    assert (W01 : wat Mm (at_off (ptr_of v) 8) w1).
    { apply wat_push_inv; [assumption|left]. rewrite u_at_off by (pose proof (word_range (ptr_of v)); unfold fromhi in *; pose proof (word_range fp); lia). unfold fromhi in *; lia. }
    destruct (pair_write_ok Mm nx (ptr_of v) w0 w1 (pair_moved nx) Hs) as (Hk & W0 & W1 & W2 & W3 & W4).
    destruct (copy_cell phi Mm a nx (ptr_of v) w0 w1 _ IM Hc W00 H3 W01 H7 Hk W0 W1 W2 W3 W4) as (Hn & _ & _ & I2).
    do 2 eexists. split; [apply fupd_extends; exact Hn|]. split; [exact I2|].
    split.
    + unfold img. rewrite Ht. simpl. unfold fupd. rewrite bv_eqb_true by reflexivity. reflexivity.
    + eexists. unfold fupd. rewrite bv_eqb_true by reflexivity. reflexivity.
  - destruct H0 as [H0a _].
    assert (Eq : q = nx) by (eapply wat_fun; [exact H5|exact (i_next _ _ _ _ I)]).
    subst q.
    pose proof (cell_from _ Hc) as [C1 C2].
    assert (Hs : slots_ok nx (ptr_of v)) by (repeat split; assumption).
    set (Mm := M fp ra s0 s1 s2 s3 m) in *.
    assert (W00 : wat Mm (ptr_of v) w0) by (apply wat_push_inv; [assumption|left; unfold fromhi in *; pose proof (word_range fp); lia]).
    assert (W01 : wat Mm (at_off (ptr_of v) 8) w1).
    { apply wat_push_inv; [assumption|left]. rewrite u_at_off by (pose proof (word_range (ptr_of v)); unfold fromhi in *; pose proof (word_range fp); lia). unfold fromhi in *; lia. }
    destruct (pair_write_ok Mm nx (ptr_of v) w0 w1 (pair_moved nx) Hs) as (Hk & W0 & W1 & W2 & W3 & W4).
    destruct (copy_cell phi Mm a nx (ptr_of v) w0 w1 _ IM Hc W00 H3 W01 H7 Hk W0 W1 W2 W3 W4) as (Hn & _ & E1 & I2).
    destruct (proj2 (cell_vals _ Hc)) as [Hnp|[_ Cn]].
    + exfalso. rewrite <- E1, H8 in Hnp. destruct Hnp as [E|[E|[E|E]]]; lia.
    + rewrite <- E1 in Cn.
      destruct (inv_spine _ _ _ _ _ H9 _ _ I2 H8 Cn) as (phi' & Hx & I3).
      assert (Hp : phi' (ptr_of v) = Some nx).
      { apply Hx. unfold fupd. rewrite bv_eqb_true by reflexivity. reflexivity. }
      exists phi', cur'. split; [eapply extends_trans; [apply fupd_extends; exact Hn|exact Hx]|].
      split; [exact I3|]. split.
      * unfold img. rewrite Ht, Hp. simpl. reflexivity.
      * exists nx. exact Hp.
  - exfalso. rewrite Ht in H. destruct H as [E|[E|E]]; lia.
Qed.

(** Advance the scan past one word whose image is now in place. *)
Lemma inv_advance : forall phi m m' a nx p q w,
  Inv phi m a nx -> phi p = Some q ->
  ((a = q /\ w = o0 p) \/ (a = at_off q 8 /\ w = o1 p)) ->
  (tag w = 3 -> exists q', phi (ptr_of w) = Some q') ->
  wat m' a (img phi w) ->
  keeps m m' [a] ->
  Inv phi m' (at_off a 8) nx.
Proof.
  intros phi m m' a nx p q w I Hp Hown Hdn Wa Hk.
  destruct I as [Inx [Tn Tb] [Ia1 Ia2] Iu Ico Iin Isu] eqn:EI.
  pose proof (Ico p q Hp) as (Cp & _ & _ & Tq & Bq & _).
  pose proof (word_range q) as Rq. pose proof (word_range fp) as Rf. pose proof (word_range c) as Rc.
  pose proof (word_range a) as Ra.
  pose proof Tq as [Tq1 Tq2].
  assert (Uq8 : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
  assert (Hau : bv_unsigned a = bv_unsigned q \/ bv_unsigned a = bv_unsigned q + 8).
  { destruct Hown as [[-> _]|[-> _]]; [left; reflexivity|right; exact Uq8]. }
  assert (Ua8 : bv_unsigned (at_off a 8) = bv_unsigned a + 8) by (apply u_at_off; lia).
  assert (Disj : forall z : word, (bv_unsigned z + 8 <= bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned z) ->
     Forall (fun x => bv_unsigned x + 8 <= bv_unsigned z \/ bv_unsigned z + 8 <= bv_unsigned x) [a]).
  { intros z Hz. apply Forall_cons; [lia|apply Forall_nil]. }
  assert (Amod : (bv_unsigned a - bv_unsigned q0) mod 8 = 0).
  { pose proof (Z_div_mod_eq_full (bv_unsigned q - bv_unsigned q0) 16) as D. rewrite Tq2 in D.
    destruct Hau as [H|H]; rewrite H.
    - replace (bv_unsigned q - bv_unsigned q0) with (2 * ((bv_unsigned q - bv_unsigned q0) / 16) * 8) by lia.
      apply Z.mod_mul; lia.
    - replace (bv_unsigned q + 8 - bv_unsigned q0) with ((2 * ((bv_unsigned q - bv_unsigned q0) / 16) + 1) * 8) by lia.
      apply Z.mod_mul; lia. }
  assert (Hword : forall (z w' : word),
     (bv_unsigned z - bv_unsigned q0) mod 8 = 0 -> bv_unsigned q0 <= bv_unsigned z ->
     bv_unsigned z + 8 <= bv_unsigned nx ->
     wat m z (show phi a z w') -> done phi a z w' -> (z = a -> w' = w) ->
     wat m' z (show phi (at_off a 8) z w') /\ done phi (at_off a 8) z w').
  { intros z w' Zm Z1 Z2 Wz Dz Hzw.
    destruct (w_dec z a) as [->|Hne].
    - rewrite (Hzw eq_refl). split.
      + unfold show. rewrite Ua8.
        assert (L : bv_unsigned a < bv_unsigned a + 8) by lia.
        rewrite (proj2 (Z.ltb_lt _ _) L). exact Wa.
      + intros _ E. exact (Hdn E).
    - assert (Hu : bv_unsigned z <> bv_unsigned a) by (intro E; apply Hne, bv_eq, E).
      pose proof (Z_div_mod_eq_full (bv_unsigned z - bv_unsigned q0) 8) as D1. rewrite Zm in D1.
      pose proof (Z_div_mod_eq_full (bv_unsigned a - bv_unsigned q0) 8) as D2. rewrite Amod in D2.
      assert (Hs : bv_unsigned z + 8 <= bv_unsigned a \/ bv_unsigned a + 8 <= bv_unsigned z) by lia.
      assert (Es : show phi (at_off a 8) z w' = show phi a z w').
      { unfold show. rewrite Ua8.
        destruct Hs as [L|L].
        - assert (L1 : bv_unsigned z < bv_unsigned a + 8) by lia.
          assert (L2 : bv_unsigned z < bv_unsigned a) by lia.
          rewrite (proj2 (Z.ltb_lt _ _) L1), (proj2 (Z.ltb_lt _ _) L2). reflexivity.
        - assert (L1 : bv_unsigned a + 8 <= bv_unsigned z) by lia.
          assert (L2 : bv_unsigned a <= bv_unsigned z) by lia.
          rewrite (proj2 (Z.ltb_ge _ _) L1), (proj2 (Z.ltb_ge _ _) L2). reflexivity. }
      rewrite Es. split.
      + eapply Hk; [exact Wz|lia|apply Disj; exact Hs].
      + intros L E. apply Dz; [|exact E]. rewrite Ua8 in L. lia. }
  constructor.
  - eapply Hk; [exact Inx|rewrite u_at_off by lia; lia|apply Disj; rewrite u_at_off by lia; lia].
  - split; assumption.
  - rewrite Ua8. lia.
  - intros x Cx Hn. destruct (Iu x Cx Hn) as [U0 U1].
    pose proof (cell_from x Cx) as [C1 C2]. pose proof (word_range x) as Rx. unfold fromhi in *.
    assert (Ux : bv_unsigned (at_off x 8) = bv_unsigned x + 8) by (apply u_at_off; lia).
    split.
    + eapply Hk; [exact U0|lia|apply Disj; lia].
    + eapply Hk; [exact U1|rewrite Ux; lia|apply Disj; rewrite Ux; lia].
  - intros x q' Hx. destruct (Ico x q' Hx) as (Cx & F0 & F1 & Tq' & Bq' & V0 & V1 & D0 & D1).
    pose proof (cell_from x Cx) as [C1 C2]. pose proof (word_range x) as Rx. pose proof (word_range q') as Rq'.
    pose proof Tq' as [Tq1' Tq2'].
    assert (Ux : bv_unsigned (at_off x 8) = bv_unsigned x + 8) by (unfold fromhi in *; apply u_at_off; lia).
    assert (Uq' : bv_unsigned (at_off q' 8) = bv_unsigned q' + 8) by (apply u_at_off; lia).
    pose proof (Z_div_mod_eq_full (bv_unsigned q - bv_unsigned q0) 16) as Da. rewrite Tq2 in Da.
    pose proof (Z_div_mod_eq_full (bv_unsigned q' - bv_unsigned q0) 16) as Db. rewrite Tq2' in Db.
    assert (M0 : (bv_unsigned q' - bv_unsigned q0) mod 8 = 0).
    { replace (bv_unsigned q' - bv_unsigned q0) with (2 * ((bv_unsigned q' - bv_unsigned q0) / 16) * 8) by lia.
      apply Z.mod_mul; lia. }
    assert (M1 : (bv_unsigned (at_off q' 8) - bv_unsigned q0) mod 8 = 0).
    { rewrite Uq'. replace (bv_unsigned q' + 8 - bv_unsigned q0) with ((2 * ((bv_unsigned q' - bv_unsigned q0) / 16) + 1) * 8) by lia.
      apply Z.mod_mul; lia. }
    assert (H0w : q' = a -> o0 x = w).
    { intro E. destruct Hown as [[Ea Ew]|[Ea Ew]].
      - assert (Eq : q' = q) by congruence. rewrite Eq in Hx.
        rewrite (Iin x p q Hx Hp). rewrite Ew. reflexivity.
      - exfalso. rewrite E, Ea, Uq8 in *. lia. }
    assert (H1w : at_off q' 8 = a -> o1 x = w).
    { intro E. destruct Hown as [[Ea Ew]|[Ea Ew]].
      - exfalso. assert (bv_unsigned (at_off q' 8) = bv_unsigned q) by (rewrite E, Ea; reflexivity). lia.
      - assert (Eq : q' = q).
        { apply bv_eq. assert (bv_unsigned (at_off q' 8) = bv_unsigned (at_off q 8)) by (rewrite E, Ea; reflexivity). lia. }
        rewrite Eq in Hx. rewrite (Iin x p q Hx Hp). rewrite Ew. reflexivity. }
    destruct (Hword q' (o0 x) M0 Tq1' ltac:(lia) V0 D0 H0w) as [Y0 Z0].
    destruct (Hword (at_off q' 8) (o1 x) M1 ltac:(rewrite Uq'; lia) ltac:(rewrite Uq'; lia) V1 D1 H1w) as [Y1 Z1].
    split; [exact Cx|]. split.
    { eapply Hk; [exact F0|unfold fromhi in *; lia|apply Disj; unfold fromhi in *; lia]. }
    split.
    { eapply Hk; [exact F1|rewrite Ux; unfold fromhi in *; lia|apply Disj; rewrite Ux; unfold fromhi in *; lia]. }
    split; [exact Tq'|]. split; [exact Bq'|].
    split; [exact Y0|]. split; [exact Y1|]. split; [exact Z0|exact Z1].
  - exact Iin.
  - exact Isu.
Qed.

Lemma keeps_refl : forall m l, keeps m m l.
Proof. intros m l a v Hw _ _. exact Hw. Qed.

Lemma img_nonptr : forall phi w, tag w <> 3 -> img phi w = w.
Proof.
  intros phi w H. unfold img. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
Qed.

Lemma show_here : forall phi a w, show phi a a w = w.
Proof.
  intros phi a w. unfold show. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(** One slot of the scan. *)
Lemma inv_slot : forall phi m m' a nx p q w ra s0v,
  Inv phi m a nx -> phi p = Some q ->
  ((a = q /\ w = o0 p) \/ (a = at_off q 8 /\ w = o1 p)) ->
  slot c from fw q0 tohi sp s1v ra s0v m a w m' ->
  exists phi' nx', extends phi phi' /\ Inv phi' m' (at_off a 8) nx'.
Proof.
  intros phi m m' a nx p q w ra s0v I Hp Hown Hs.
  pose proof (i_copied _ _ _ _ I p q Hp) as (Cp & _ & _ & Tq & Bq & V0 & V1 & _).
  pose proof (word_range q) as Rq. pose proof (word_range a) as Ra. pose proof (word_range fp) as Rf.
  pose proof (i_nx _ _ _ _ I) as [_ Tb].
  assert (Uq8 : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
  assert (Wa : wat m a w).
  { destruct Hown as [[-> ->]|[-> ->]].
    - rewrite show_here in V0. exact V0.
    - rewrite show_here in V1. exact V1. }
  assert (Hv : val_ok w).
  { destruct (cell_vals p Cp) as [A B]. destruct Hown as [[_ ->]|[_ ->]]; assumption. }
  destruct Hs as [Hn|m0 res Hip Hcv].
  - assert (Ht : tag w <> 3).
    { destruct Hn as [E|[E|[E|E]]]; rewrite E; lia. }
    exists phi, nx. split; [apply extends_refl|].
    eapply inv_advance; [exact I|exact Hp|exact Hown| |rewrite img_nonptr by exact Ht; exact Wa|apply keeps_refl].
    intro E. contradiction.
  - destruct Hv as [Hn|[Ht Cw]].
    + exfalso. destruct Hip as [E|[E|[E|E]]]; destruct Hn as [F|[F|[F|F]]]; lia.
    + destruct (inv_call _ _ _ _ _ phi m a nx w m0 res I Ht Cw Hcv) as (phi' & nx' & Hx & I2 & Er & Hq').
      exists phi', nx'. split; [exact Hx|].
      pose proof (Hx p q Hp) as Hp'.
      pose proof (i_nx _ _ _ _ I2) as [_ Tb2].
      pose proof (i_copied _ _ _ _ I2 p q Hp') as (_ & _ & _ & _ & Bq2 & _).
      assert (Hau : bv_unsigned a + 8 <= bv_unsigned nx').
      { destruct Hown as [[-> _]|[-> _]]; rewrite ?Uq8; lia. }
      eapply inv_advance; [exact I2|exact Hp'|exact Hown|exact (fun _ => Hq')| |].
      * rewrite <- Er. apply wat_hit. lia.
      * intros z y Hz Hb Hf. inversion Hf as [|? ? Pz _]; subst.
        apply write_keep; [exact Hz|exact Hb|lia|exact Pz].
Qed.

Lemma at_off_add : forall (s : word), bv_unsigned s + 16 < 2^64 -> at_off (at_off s 8) 8 = at_off s 16.
Proof.
  intros s Hb. pose proof (word_range s). apply bv_eq.
  rewrite !u_at_off by (rewrite ?u_at_off by lia; lia). lia.
Qed.

(** One pair of the scan: both slots. *)
Lemma inv_pair : forall phi m s nx s0v m2,
  Inv phi m s nx -> to_cell s -> bv_unsigned s < bv_unsigned nx ->
  pair_body c from fw q0 tohi sp s1v m s s0v m2 ->
  exists phi' nx', extends phi phi' /\ Inv phi' m2 (at_off s 16) nx'.
Proof.
  intros phi m s nx s0v m2 I Ts Ls (a0 & a1 & m1 & W0 & _ & Sl0 & W1 & Sl1).
  destruct (i_surj _ _ _ _ I s Ts Ls) as (p & Hp).
  pose proof (i_copied _ _ _ _ I p s Hp) as (Cp & _ & _ & _ & Bq & V0 & _).
  rewrite show_here in V0.
  assert (E0 : a0 = o0 p) by exact (wat_fun _ _ _ _ W0 V0). subst a0.
  destruct (inv_slot phi m m1 s nx p s (o0 p) _ _ I Hp (or_introl (conj eq_refl eq_refl)) Sl0)
    as (phi1 & nx1 & Hx1 & I1).
  pose proof (Hx1 p s Hp) as Hp1.
  pose proof (i_copied _ _ _ _ I1 p s Hp1) as (_ & _ & _ & _ & Bq1 & _ & V1 & _).
  rewrite show_here in V1.
  assert (E1 : a1 = o1 p) by exact (wat_fun _ _ _ _ W1 V1). subst a1.
  destruct (inv_slot phi1 m1 m2 (at_off s 8) nx1 p s (o1 p) _ _ I1 Hp1 (or_intror (conj eq_refl eq_refl)) Sl1)
    as (phi2 & nx2 & Hx2 & I2).
  pose proof (i_nx _ _ _ _ I1) as [_ Tb1]. pose proof (word_range fp) as Rf.
  rewrite at_off_add in I2 by lia.
  exists phi2, nx2. split; [eapply extends_trans; eassumption|exact I2].
Qed.

(** The invariant across the whole scan. *)
Lemma inv_scan : forall m s s0v m' s',
  scan_pairs c from fw q0 tohi sp s1v m s s0v m' s' ->
  forall phi nx, Inv phi m s nx -> to_cell s -> bv_unsigned s < bv_unsigned nx ->
  exists phi' nx', extends phi phi' /\ Inv phi' m' s' nx' /\ bv_unsigned nx' <= bv_unsigned s'.
Proof.
  induction 1; intros phi nx' I Ts Ls.
  - destruct (inv_pair phi m s nx' s0v m2 I Ts Ls H) as (phi2 & nx2 & Hx & I2).
    assert (En : nx = nx2) by exact (wat_fun _ _ _ _ H2 (i_next _ _ _ _ I2)). subst nx2.
    pose proof (word_range s) as Rs. pose proof (word_range fp) as Rf.
    exists phi2, nx. split; [exact Hx|]. split; [exact I2|].
    rewrite u_at_off by lia. exact H3.
  - destruct (inv_pair phi m s nx' s0v m2 I Ts Ls H) as (phi2 & nx2 & Hx & I2).
    assert (En : nx = nx2) by exact (wat_fun _ _ _ _ H2 (i_next _ _ _ _ I2)). subst nx2.
    pose proof (word_range s) as Rs. pose proof (word_range fp) as Rf.
    assert (Us : bv_unsigned (at_off s 16) = bv_unsigned s + 16) by (apply u_at_off; lia).
    destruct (IHscan_pairs phi2 nx I2 (to_add16 s Ts ltac:(lia)) ltac:(rewrite Us; exact H3))
      as (phi3 & nx3 & Hx3 & I3 & Le).
    exists phi3, nx3. split; [eapply extends_trans; eassumption|]. split; [exact I3|exact Le].
Qed.

(** Reachability in the original graph. *)
Inductive reach (r : word) : word -> Prop :=
| reach_root : reach r r
| reach_head : forall p, reach r p -> tag (o0 p) = 3 -> reach r (ptr_of (o0 p))
| reach_tail : forall p, reach r p -> tag (o1 p) = 3 -> reach r (ptr_of (o1 p)).

(** THEOREM: at the end of the scan, the forwarding map is an isomorphism between what
    was reachable and all of to-space. *)
Theorem scan_iso : forall phi m s s0v m' s' nx,
  scan_pairs c from fw q0 tohi sp s1v m s s0v m' s' ->
  Inv phi m s nx -> to_cell s -> bv_unsigned s < bv_unsigned nx ->
  exists phi', extends phi phi' /\
    (* Every to-space cell comes from exactly one from-space cell. *)
    (forall p p' q, phi' p = Some q -> phi' p' = Some q -> p = p') /\
    (forall q, to_cell q -> bv_unsigned q < bv_unsigned s' -> exists p, phi' p = Some q) /\
    (* Each copy holds the images of the original's values, and the original forwards. *)
    (forall p q, phi' p = Some q ->
       cell p /\ to_cell q /\ bv_unsigned q + 16 <= bv_unsigned s' /\
       wat m' q (img phi' (o0 p)) /\ wat m' (at_off q 8) (img phi' (o1 p)) /\
       wat m' p V_FORWARD /\ wat m' (at_off p 8) (pair_moved q)) /\
    (* Everything reachable from a forwarded root is forwarded. *)
    (forall r p q, phi' r = Some q -> reach r p -> exists q', phi' p = Some q').
Proof.
  intros phi m s s0v m' s' nx Hs I Ts Ls.
  destruct (inv_scan m s s0v m' s' Hs phi nx I Ts Ls) as (phi' & nx' & Hx & I2 & Le).
  pose proof (i_a _ _ _ _ I2) as [Ia1 Ia2].
  assert (Es : bv_unsigned s' = bv_unsigned nx') by lia.
  pose proof (i_nx _ _ _ _ I2) as [_ Tb]. pose proof (word_range fp) as Rf.
  assert (Done : forall p q, phi' p = Some q ->
     wat m' q (img phi' (o0 p)) /\ wat m' (at_off q 8) (img phi' (o1 p)) /\
     (tag (o0 p) = 3 -> exists z, phi' (ptr_of (o0 p)) = Some z) /\
     (tag (o1 p) = 3 -> exists z, phi' (ptr_of (o1 p)) = Some z)).
  { intros p q Hp.
    pose proof (i_copied _ _ _ _ I2 p q Hp) as (_ & _ & _ & _ & Bq & V0 & V1 & D0 & D1).
    pose proof (word_range q) as Rq.
    assert (Uq : bv_unsigned (at_off q 8) = bv_unsigned q + 8) by (apply u_at_off; lia).
    assert (L0 : bv_unsigned q < bv_unsigned s') by lia.
    assert (L1 : bv_unsigned (at_off q 8) < bv_unsigned s') by (rewrite Uq; lia).
    unfold show in V0, V1.
    rewrite (proj2 (Z.ltb_lt _ _) L0) in V0. rewrite (proj2 (Z.ltb_lt _ _) L1) in V1.
    split; [exact V0|]. split; [exact V1|]. split; intro E; [exact (D0 L0 E)|exact (D1 L1 E)]. }
  exists phi'. split; [exact Hx|]. split; [exact (i_inj _ _ _ _ I2)|].
  split.
  { intros q Tq Lq. apply (i_surj _ _ _ _ I2 q Tq). lia. }
  split.
  { intros p q Hp. pose proof (i_copied _ _ _ _ I2 p q Hp) as (Cp & F0 & F1 & Tq & Bq & _).
    destruct (Done p q Hp) as (V0 & V1 & _).
    split; [exact Cp|]. split; [exact Tq|]. split; [lia|]. split; [exact V0|]. split; [exact V1|].
    split; assumption. }
  intros r p q Hr Hreach. induction Hreach.
  - exists q. exact Hr.
  - destruct IHHreach as (z & Hz). destruct (Done p z Hz) as (_ & _ & D0 & _). exact (D0 H).
  - destruct IHHreach as (z & Hz). destruct (Done p z Hz) as (_ & _ & _ & D1). exact (D1 H).
Qed.

End Graph.
