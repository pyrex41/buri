(* E2E-21 (CL side): a small A64 instruction decoder and integer semantics,
   just large enough for the type-test code the pinned SBCL 2.6.8 arm64
   image emits for the host operations of CLContracts.cl_host_ops
   (ports/repr/sbcl/sbcl-2.6.8-arm64-type-tests.capture).

   Trust boundary (stated, not proved): [decode] and [step] are a
   transcription of the Arm A64 encodings and pseudocode (Arm ARM DDI 0487)
   for the forms below; anything else decodes to [None] or has no step, so an
   unsupported instruction makes [run] fail instead of guessing. Registers
   hold integers in [0, 2^64); register 31 reads as zero where the
   architecture says ZR, and every form whose register 31 means SP is
   refused (no window touches SP). Flags follow AddWithCarry exactly.
   Memory is a byte function, read only: no form here stores.

   Uses only the Coq standard library. *)
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
Module SbclA64.

Definition fld (w lo len : Z) : Z := Z.land (Z.shiftr w lo) (Z.ones len).
Definition sext (x n : Z) : Z := if Z.testbit x (n - 1) then x - 2 ^ n else x.

Inductive cond := CEQ | CNE | CCS | CCC | CMI | CPL | CVS | CVC | CHI | CLS | CGE | CLT
 | CGT | CLE | CAL | CNV.
Definition cond_of (c : Z) : cond :=
 match c with 0 => CEQ | 1 => CNE | 2 => CCS | 3 => CCC | 4 => CMI | 5 => CPL | 6 => CVS
 | 7 => CVC | 8 => CHI | 9 => CLS | 10 => CGE | 11 => CLT | 12 => CGT | 13 => CLE
 | 14 => CAL | _ => CNV end.

Inductive instr :=
 | ILogImm (sf : bool) (opc rd rn imm : Z)          (* AND ORR EOR ANDS (immediate) *)
 | IAddSubImm (sf sub setf : bool) (rd rn imm : Z)  (* ADD SUB ADDS SUBS (immediate) *)
 | IAddSubReg (sf sub setf : bool) (rd rn rm : Z)   (* ... (shifted register), LSL #0 *)
 | ILogReg (sf : bool) (opc rd rn rm : Z)           (* AND ORR EOR ANDS (shifted register), LSL #0 *)
 | ICcmpReg (sf : bool) (rn rm nzcv : Z) (c : cond) (* CCMP (register) *)
 | ICsel (sf : bool) (rd rn rm : Z) (c : cond)      (* CSEL *)
 | ITb (nz : bool) (rt b off : Z)                   (* TBZ / TBNZ; off in instructions *)
 | IBcond (c : cond) (off : Z)                      (* B.cond *)
 | IB (off : Z)                                     (* B *)
 | ILdurb (rt rn simm : Z)                          (* LDURB (LDRB with unscaled offset) *)
 | ILdrX (rt rn off : Z) | IStrX (rt rn off : Z)    (* LDR/STR Xt, [Xn, #off] (unsigned offset) *)
 | ILdpX (rt rt2 rn off : Z)                        (* LDP Xt, Xt2, [Xn, #off] (signed offset) *)
 | IRet (rn : Z).

(* DecodeBitMasks(N, imms, immr, TRUE, datasize). *)
Fixpoint replicate (e esize : Z) (k : nat) : Z :=
 match k with O => 0 | S k => Z.lor (Z.shiftl e (esize * Z.of_nat k)) (replicate e esize k) end.
Definition ror (x r size : Z) : Z :=
 Z.land (Z.lor (Z.shiftr x r) (Z.shiftl x (size - r))) (Z.ones size).
Definition bitmask (datasize n imms immr : Z) : option Z :=
 let comb := n * 64 + (63 - imms) in
 if comb <=? 0 then None else
 let len := Z.log2 comb in
 if len <? 1 then None else
 let levels := Z.ones len in
 if Z.land imms levels =? levels then None else
 let s := Z.land imms levels in
 let r := Z.land immr levels in
 let esize := 2 ^ len in
 if datasize <? esize then None else
 Some (replicate (ror (Z.ones (s + 1)) r esize) esize (Z.to_nat (datasize / esize))).

Definition decode (w : Z) : option instr :=
 let sf := Z.testbit w 31 in
 let rd := fld w 0 5 in let rn := fld w 5 5 in let rm := fld w 16 5 in
 if fld w 23 6 =? 36 then
   (if negb sf && Z.testbit w 22 then None else
    match bitmask (if sf then 64 else 32) (fld w 22 1) (fld w 10 6) (fld w 16 6) with
    | Some imm => Some (ILogImm sf (fld w 29 2) rd rn imm) | None => None end)
 else if fld w 23 6 =? 34 then
   Some (IAddSubImm sf (Z.testbit w 30) (Z.testbit w 29) rd rn
                    (Z.shiftl (fld w 10 12) (12 * fld w 22 1)))
 else if (fld w 24 5 =? 11) && negb (Z.testbit w 21) then
   (if (fld w 22 2 =? 0) && (fld w 10 6 =? 0)
    then Some (IAddSubReg sf (Z.testbit w 30) (Z.testbit w 29) rd rn rm) else None)
 else if fld w 24 5 =? 10 then
   (if (fld w 22 2 =? 0) && negb (Z.testbit w 21) && (fld w 10 6 =? 0)
    then Some (ILogReg sf (fld w 29 2) rd rn rm) else None)
 else if (fld w 21 8 =? 210) && Z.testbit w 29 && negb (Z.testbit w 11) && negb (Z.testbit w 10)
         && negb (Z.testbit w 4) then
   (if Z.testbit w 30 then Some (ICcmpReg sf rn rm (fld w 0 4) (cond_of (fld w 12 4))) else None)
 else if (fld w 21 8 =? 212) && negb (Z.testbit w 30) && negb (Z.testbit w 29) && (fld w 10 2 =? 0) then
   Some (ICsel sf rd rn rm (cond_of (fld w 12 4)))
 else if fld w 25 6 =? 27 then
   Some (ITb (Z.testbit w 24) rd (fld w 31 1 * 32 + fld w 19 5) (sext (fld w 5 14) 14))
 else if (fld w 24 8 =? 84) && negb (Z.testbit w 4) then
   Some (IBcond (cond_of (fld w 0 4)) (sext (fld w 5 19) 19))
 else if fld w 26 6 =? 5 then Some (IB (sext (fld w 0 26) 26))
 else if (fld w 21 11 =? 450) && (fld w 10 2 =? 0) then Some (ILdurb rd rn (sext (fld w 12 9) 9))
 else if fld w 22 10 =? 997 then Some (ILdrX rd rn (8 * fld w 10 12))
 else if fld w 22 10 =? 996 then Some (IStrX rd rn (8 * fld w 10 12))
 else if fld w 22 10 =? 677 then Some (ILdpX rd (fld w 10 5) rn (8 * sext (fld w 15 7) 7))
 else if (fld w 10 22 =? 3512256) && (fld w 0 5 =? 0) then Some (IRet rn)
 else None.

Fixpoint decode_all (ws : list Z) : option (list instr) :=
 match ws with
 | [] => Some []
 | w :: ws => match decode w, decode_all ws with Some i, Some is => Some (i :: is) | _, _ => None end end.

(* ---------------------------------------------------------------- semantics *)

Record state := { R : Z -> Z; fN : bool; fZ : bool; fC : bool; fV : bool }.
Definition regs_ok (s : state) : Prop := forall r, 0 <= R s r < 2 ^ 64.

Definition width (sf : bool) : Z := if sf then 64 else 32.
Definition trunc (n x : Z) : Z := x mod 2 ^ n.
Definition sint (n x : Z) : Z := let u := trunc n x in if u <? 2 ^ (n - 1) then u else u - 2 ^ n.
(* Register 31 as ZR. *)
Definition rz (s : state) (r : Z) : Z := if r =? 31 then 0 else R s r.
Definition setr (s : state) (r v : Z) : state :=
 if r =? 31 then s else
 {| R := fun i => if i =? r then v else R s i; fN := fN s; fZ := fZ s; fC := fC s; fV := fV s |}.
Definition setf (s : state) (n z c v : bool) : state :=
 {| R := R s; fN := n; fZ := z; fC := c; fV := v |}.

(* AddWithCarry(x, y, carry) on n-bit operands: result and N, Z, C, V. *)
Definition awc (n x y c : Z) : Z * (bool * bool * bool * bool) :=
 let us := trunc n x + trunc n y + c in
 let ss := sint n x + sint n y + c in
 let r := trunc n us in
 (r, (Z.testbit r (n - 1), r =? 0, negb (r =? us), negb (sint n r =? ss))).
Definition addsub (n : Z) (sub : bool) (x y : Z) :=
 if sub then awc n x (Z.ones n - trunc n y) 1 else awc n x y 0.

Definition holds (s : state) (c : cond) : bool :=
 match c with
 | CEQ => fZ s | CNE => negb (fZ s) | CCS => fC s | CCC => negb (fC s)
 | CMI => fN s | CPL => negb (fN s) | CVS => fV s | CVC => negb (fV s)
 | CHI => fC s && negb (fZ s) | CLS => negb (fC s && negb (fZ s))
 | CGE => Bool.eqb (fN s) (fV s) | CLT => negb (Bool.eqb (fN s) (fV s))
 | CGT => negb (fZ s) && Bool.eqb (fN s) (fV s) | CLE => negb (negb (fZ s) && Bool.eqb (fN s) (fV s))
 | CAL | CNV => true end.

Definition logop (opc a b : Z) : Z :=
 if opc =? 1 then Z.lor a b else if opc =? 2 then Z.lxor a b else Z.land a b.

(* One step: the next state and the pc delta (in instructions). *)
Definition step (m : Z -> Z) (i : instr) (s : state) : option (state * Z) :=
 match i with
 | ILogImm sf opc rd rn imm =>
     let n := width sf in let r := trunc n (logop opc (rz s rn) imm) in
     if opc =? 3 then Some (setr (setf s (Z.testbit r (n - 1)) (r =? 0) false false) rd r, 1)
     else if rd =? 31 then None else Some (setr s rd r, 1)
 | IAddSubImm sf sub sf' rd rn imm =>
     if rn =? 31 then None else
     let '(r, (fn, fz, fc, fv)) := addsub (width sf) sub (R s rn) imm in
     if sf' then Some (setr (setf s fn fz fc fv) rd r, 1)
     else if rd =? 31 then None else Some (setr s rd r, 1)
 | IAddSubReg sf sub sf' rd rn rm =>
     let '(r, (fn, fz, fc, fv)) := addsub (width sf) sub (rz s rn) (rz s rm) in
     Some (setr (if sf' then setf s fn fz fc fv else s) rd r, 1)
 | ILogReg sf opc rd rn rm =>
     let n := width sf in let r := trunc n (logop opc (rz s rn) (rz s rm)) in
     Some (setr (if opc =? 3 then setf s (Z.testbit r (n - 1)) (r =? 0) false false else s) rd r, 1)
 | ICcmpReg sf rn rm nzcv c =>
     if holds s c then
       let '(_, (fn, fz, fc, fv)) := addsub (width sf) true (rz s rn) (rz s rm) in Some (setf s fn fz fc fv, 1)
     else Some (setf s (Z.testbit nzcv 3) (Z.testbit nzcv 2) (Z.testbit nzcv 1) (Z.testbit nzcv 0), 1)
 | ICsel sf rd rn rm c =>
     Some (setr s rd (trunc (width sf) (if holds s c then rz s rn else rz s rm)), 1)
 | ITb nz rt b off => Some (s, if Bool.eqb (Z.testbit (rz s rt) b) nz then off else 1)
 | IBcond c off => Some (s, if holds s c then off else 1)
 | IB off => Some (s, off)
 | ILdurb rt rn simm =>
     if rn =? 31 then None else Some (setr s rt (m (trunc 64 (R s rn + simm)) mod 256), 1)
 | _ => None end.

(* Run a window of instructions from index pc; leaving at index = length
   (falling or branching to the instruction after the window) is the exit.
   Exhausted fuel, a branch outside [0, length] or an unsupported step fail. *)
Fixpoint nth_z {A} (l : list A) (k : Z) : option A :=
 match l with [] => None | x :: l => if k =? 0 then Some x else nth_z l (k - 1) end.

Fixpoint run (fuel : nat) (m : Z -> Z) (p : list instr) (pc : Z) (s : state) : option state :=
 match fuel with
 | O => None
 | S f =>
   if pc =? Z.of_nat (length p) then Some s
   else if pc <? 0 then None
   else match nth_z p pc with
        | None => None
        | Some i => match step m i s with
                    | Some (s', d) => run f m p (pc + d) s'
                    | None => None end end end.

Definition run_words (fuel : nat) (m : Z -> Z) (ws : list Z) (s : state) : option state :=
 match decode_all ws with Some p => run fuel m p 0 s | None => None end.

(* ---------------------------------------------------------------- flag facts *)

Lemma trunc_small : forall n x, 0 <= n -> 0 <= x < 2 ^ n -> trunc n x = x.
Proof. intros n x Hn H. unfold trunc. apply Z.mod_small. exact H. Qed.

(* SUBS on n-bit operands in range: Z is equality, C is unsigned >=. *)
Theorem sub_flags_zc : forall n a b, 1 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n ->
  let '(_, (_, z, c, _)) := addsub n true a b in z = (a =? b) /\ c = (b <=? a).
Proof.
  intros n a b Hn Ha Hb. unfold addsub, awc.
  rewrite (trunc_small n a), (trunc_small n b) by lia.
  assert (Hp : 0 < 2 ^ n) by lia.
  rewrite Z.ones_equiv. unfold trunc.
  rewrite (Z.mod_small (Z.pred (2 ^ n) - b) (2 ^ n)) by lia.
  replace (a + (Z.pred (2 ^ n) - b) + 1) with (a - b + 2 ^ n) by lia.
  destruct (Z.le_gt_cases b a).
  - rewrite <- (Z.mod_unique (a - b + 2 ^ n) (2 ^ n) 1 (a - b)) by lia.
    split; [|apply Z.leb_le in H; rewrite H; apply negb_true_iff, Z.eqb_neq; lia].
    destruct (Z.eqb_spec (a - b) 0), (Z.eqb_spec a b); try reflexivity; lia.
  - rewrite Z.mod_small by lia.
    split.
    + destruct (Z.eqb_spec (a - b + 2 ^ n) 0), (Z.eqb_spec a b); try reflexivity; lia.
    + assert (E : (b <=? a) = false) by (apply Z.leb_gt; lia). rewrite E.
      rewrite Z.eqb_refl. reflexivity.
Qed.

(* SUBS on operands that are nonnegative as signed n-bit values: N = V iff a >= b. *)
Theorem sub_flags_nv : forall n a b, 1 <= n -> 0 <= a < 2 ^ (n - 1) -> 0 <= b < 2 ^ (n - 1) ->
  let '(_, (fn, _, _, fv)) := addsub n true a b in Bool.eqb fn fv = (b <=? a).
Proof.
  intros n a b Hn Ha Hb.
  assert (E2 : 2 ^ n = 2 * 2 ^ (n - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  unfold addsub, awc, sint.
  rewrite (trunc_small n a), (trunc_small n b) by lia.
  rewrite Z.ones_equiv, <- Z.sub_1_r. unfold trunc.
  rewrite (Z.mod_small ((2 ^ n - 1) - b) (2 ^ n)) by lia.
  rewrite ?(Z.mod_small a (2 ^ n)) by lia.
  rewrite ?(Z.mod_small ((2 ^ n - 1) - b) (2 ^ n)) by lia.
  replace (a + ((2 ^ n - 1) - b) + 1) with (a - b + 2 ^ n) by lia.
  rewrite Zmod_mod.
  assert (Ha' : (a <? 2 ^ (n - 1)) = true) by (apply Z.ltb_lt; lia). rewrite Ha'.
  assert (Hb' : ((2 ^ n - 1) - b <? 2 ^ (n - 1)) = false) by (apply Z.ltb_ge; lia). rewrite Hb'.
  destruct (Z.le_gt_cases b a).
  - rewrite <- (Z.mod_unique (a - b + 2 ^ n) (2 ^ n) 1 (a - b)) by lia.
    assert (L : (a - b <? 2 ^ (n - 1)) = true) by (apply Z.ltb_lt; lia). rewrite L.
    assert (N : Z.testbit (a - b) (n - 1) = false).
    { rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity. }
    rewrite N. assert (V : (a - b =? a + ((2 ^ n - 1) - b - 2 ^ n) + 1) = true) by (apply Z.eqb_eq; lia).
    rewrite V. apply Z.leb_le in H. rewrite H. reflexivity.
  - rewrite (Z.mod_small (a - b + 2 ^ n) (2 ^ n)) by lia.
    assert (L : (a - b + 2 ^ n <? 2 ^ (n - 1)) = false) by (apply Z.ltb_ge; lia). rewrite L.
    assert (N : Z.testbit (a - b + 2 ^ n) (n - 1) = true).
    { rewrite Z.testbit_true by lia.
      replace ((a - b + 2 ^ n) / 2 ^ (n - 1)) with 1; [reflexivity|].
      apply (Z.div_unique _ _ 1 (a - b + 2 ^ (n - 1))); lia. }
    rewrite N. assert (V : (a - b + 2 ^ n - 2 ^ n =? a + ((2 ^ n - 1) - b - 2 ^ n) + 1) = true)
      by (apply Z.eqb_eq; lia).
    rewrite V. assert (G : (b <=? a) = false) by (apply Z.leb_gt; lia). rewrite G. reflexivity.
Qed.

(* Named projections of AddWithCarry, so symbolic execution can keep them
   folded and rewrite them with the facts below. *)
Definition as_r n sub x y := fst (addsub n sub x y).
Definition as_n n sub x y := fst (fst (fst (snd (addsub n sub x y)))).
Definition as_z n sub x y := snd (fst (fst (snd (addsub n sub x y)))).
Definition as_c n sub x y := snd (fst (snd (addsub n sub x y))).
Definition as_v n sub x y := snd (snd (addsub n sub x y)).
Lemma addsub_eta : forall n sub x y,
  addsub n sub x y = (as_r n sub x y, (as_n n sub x y, as_z n sub x y, as_c n sub x y, as_v n sub x y)).
Proof. intros. unfold as_r, as_n, as_z, as_c, as_v. destruct (addsub n sub x y) as [r [[[a b] c] d]]. reflexivity. Qed.
Lemma as_r_add : forall n x y, as_r n false x y = trunc n (trunc n x + trunc n y).
Proof. intros. unfold as_r, addsub, awc. cbn. rewrite Z.add_0_r. reflexivity. Qed.
Lemma as_r_sub : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> as_r n true x y = trunc n (x - y).
Proof.
  intros n x y Hn Hx Hy. unfold as_r, addsub, awc. cbn. rewrite Z.ones_equiv, <- Z.sub_1_r.
  rewrite (trunc_small n x), (trunc_small n y), (trunc_small n (2 ^ n - 1 - y)) by lia.
  unfold trunc. replace (x + (2 ^ n - 1 - y) + 1) with (x - y + 1 * 2 ^ n) by lia.
  apply Z.mod_add. lia.
Qed.
Lemma as_z_sub : forall n x y, 1 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> as_z n true x y = (x =? y).
Proof.
  intros n x y Hn Hx Hy. pose proof (sub_flags_zc n x y Hn Hx Hy) as F. unfold as_z.
  destruct (addsub n true x y) as [r [[[a b] c] d]]. apply F.
Qed.
Lemma as_c_sub : forall n x y, 1 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> as_c n true x y = (y <=? x).
Proof.
  intros n x y Hn Hx Hy. pose proof (sub_flags_zc n x y Hn Hx Hy) as F. unfold as_c.
  destruct (addsub n true x y) as [r [[[a b] c] d]]. apply F.
Qed.
Lemma as_nv_sub : forall n x y, 1 <= n -> 0 <= x < 2 ^ (n - 1) -> 0 <= y < 2 ^ (n - 1) ->
  Bool.eqb (as_n n true x y) (as_v n true x y) = (y <=? x).
Proof.
  intros n x y Hn Hx Hy. pose proof (sub_flags_nv n x y Hn Hx Hy) as F. unfold as_n, as_v.
  destruct (addsub n true x y) as [r [[[a b] c] d]]. apply F.
Qed.

(* AddWithCarry reads only the low n bits of its operands. *)
Lemma trunc_trunc : forall n x, trunc n (trunc n x) = trunc n x.
Proof. intros. unfold trunc. apply Zmod_mod. Qed.
Lemma trunc_rng : forall n x, 0 <= n -> 0 <= trunc n x < 2 ^ n.
Proof. intros n x Hn. unfold trunc. apply Z.mod_pos_bound. lia. Qed.
Lemma sint_trunc : forall n x, sint n (trunc n x) = sint n x.
Proof. intros. unfold sint. rewrite trunc_trunc. reflexivity. Qed.
Lemma addsub_trunc : forall n sub x y, addsub n sub x y = addsub n sub (trunc n x) (trunc n y).
Proof.
  intros n sub x y. unfold addsub, awc. destruct sub; rewrite ?sint_trunc, ?trunc_trunc; reflexivity.
Qed.
Lemma as_z_t : forall n x y, 1 <= n -> as_z n true x y = (trunc n x =? trunc n y).
Proof.
  intros n x y Hn. unfold as_z. rewrite addsub_trunc. fold (as_z n true (trunc n x) (trunc n y)).
  apply as_z_sub; [lia | apply trunc_rng | apply trunc_rng]; lia.
Qed.
Lemma as_c_t : forall n x y, 1 <= n -> as_c n true x y = (trunc n y <=? trunc n x).
Proof.
  intros n x y Hn. unfold as_c. rewrite addsub_trunc. fold (as_c n true (trunc n x) (trunc n y)).
  apply as_c_sub; [lia | apply trunc_rng | apply trunc_rng]; lia.
Qed.
Lemma as_r_sub_t : forall n x y, 0 <= n -> as_r n true x y = trunc n (trunc n x - trunc n y).
Proof.
  intros n x y Hn. unfold as_r. rewrite addsub_trunc. fold (as_r n true (trunc n x) (trunc n y)).
  apply as_r_sub; [lia | apply trunc_rng | apply trunc_rng]; lia.
Qed.
Lemma as_nv_t : forall n x y, 1 <= n -> trunc n x < 2 ^ (n - 1) -> trunc n y < 2 ^ (n - 1) ->
  Bool.eqb (as_n n true x y) (as_v n true x y) = (trunc n y <=? trunc n x).
Proof.
  intros n x y Hn Hx Hy. unfold as_n, as_v. rewrite addsub_trunc.
  fold (as_n n true (trunc n x) (trunc n y)). fold (as_v n true (trunc n x) (trunc n y)).
  pose proof (trunc_rng n x) as Rx. pose proof (trunc_rng n y) as Ry.
  apply as_nv_sub; lia.
Qed.

End SbclA64.
