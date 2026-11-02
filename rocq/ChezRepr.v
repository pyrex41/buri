(* E2E-21: representation relation between KLambda values (KLValue) and
   Chez Scheme 10.3.0 tarm64le machine words and memory.

   Scope (stated precisely; see docs/REPRESENTATION.md):
   * one memory snapshot `m` (bytes, little endian) and one vector-location
     map `loc`; nothing here is about how the snapshot changes (allocation,
     GC moves, mutation, other threads: E2E-25/E2E-28);
   * closures, streams and exception objects are related through the
     parameters `proc`, `port`, `cond`, whose meaning is owed by E2E-22
     (compiled code), E2E-27 (ports) and E2E-17/24 (conditions). The relation
     fixes only their machine shape (tag, header);
   * every layout number is a ChezLayout constant generated from the pinned
     sources; the ground lemmas below check them, the rest are universal.

   This is a relation about the reference representation of Shen-Scheme on
   Chez tarm64le. It is not a theorem that Shen-Scheme preserves it. *)
From Coq Require Import ZArith List Lia Bool.
From Buri Require Import Observation KLSyntax KLValue ChezLayout ChezWord.
Import ListNotations.
Open Scope Z_scope.
Module ChezRepr.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue ChezLayout.ChezLayout ChezWord.ChezWord.

(* ---------------------------------------------------------------- ground checks *)

(* Ground derivation: the cmacros.ss literals, the generated equates.h and the
   c/types.h TYPE macro agree, and the build is tarm64le, threaded, little endian. *)
Lemma chez_sources_agree :
  cm_type_pair = type_pair /\ cm_type_flonum = type_flonum /\ cm_type_symbol = type_symbol /\
  cm_type_closure = type_closure /\ cm_type_immediate = type_immediate /\
  cm_type_typed_object = type_typed_object /\ cm_type_boolean = type_boolean /\
  cm_sfalse = sfalse /\ cm_strue = strue /\ cm_type_char = type_char /\ cm_sunbound = sunbound /\
  cm_snil = snil /\ cm_seof = seof /\ cm_svoid = svoid /\ cm_sbwp = sbwp /\
  cm_type_string = type_string /\ cm_type_bignum = type_bignum /\
  cm_type_positive_bignum = type_positive_bignum /\ cm_type_negative_bignum = type_negative_bignum /\
  cm_type_code = type_code /\ cm_type_port = type_port /\ cm_type_record = type_record /\
  cm_string_char_bits = string_char_bits /\ cm_string_char_bytes = string_char_bytes /\
  cm_string_length_offset = string_length_offset /\ cm_bignum_sign_offset = bignum_sign_offset /\
  cm_bignum_length_offset = bignum_length_offset /\ cm_bigit_bits = bigit_bits /\
  cm_char_data_offset = char_data_offset /\ char_factor = 2 ^ char_data_offset /\
  c_TYPE_is_minus_typemod = 1 /\ machine_type = machine_type_tarm64le /\
  def_machine_tarm64le = 1 /\ def_pthreads = 1 /\ def_little_endian = 1 /\
  byte_alignment = 2 * ptr_bytes /\ ptr_bytes = 8.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Ground derivation: arm64.ss register assignment used by generated code. *)
Lemma chez_register_layout :
  reg_tc = 19 /\ reg_sfp = 20 /\ reg_ap = 21 /\ reg_trap = 22 /\ reg_ac0 = 23 /\ reg_xp = 24 /\
  reg_ts = 8 /\ reg_td = 25 /\ reg_cp = 26 /\ reg_jmptmp = 10 /\ reg_lr = 30 /\ reg_sp = 31 /\
  reg_arg1 = 0 /\ reg_arg2 = 1 /\ reg_arg3 = 2 /\ def_asm_arg_reg_cnt = 3 /\
  reg_extra_count = def_asm_arg_reg_max.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Ground derivation: the object-layout numbers used below. *)
Lemma chez_object_layout :
  typemod = 8 /\ byte_alignment = 16 /\ type_pair = 1 /\ type_flonum = 2 /\ type_symbol = 3 /\
  type_closure = 5 /\ type_immediate = 6 /\ type_typed_object = 7 /\
  strue = 14 /\ sfalse = 6 /\ snil = 38 /\ svoid = 46 /\ sunbound = 30 /\ seof = 54 /\
  sbwp = 78 /\ black_hole = 70 /\ forward_marker = 62 /\ type_char = 22 /\ char_factor = 256 /\
  pair_car_disp = 7 /\ pair_cdr_disp = 15 /\
  string_type_disp = 1 /\ vector_type_disp = 1 /\ bignum_type_disp = 1 /\ record_type_disp = 1 /\
  port_type_disp = 1 /\ code_type_disp = 1 /\
  mask_string = 7 /\ type_string = 2 /\ mask_vector = 7 /\ type_vector = 0 /\
  mask_bignum = 31 /\ type_bignum = 6 /\ mask_record = 7 /\ type_record = 7 /\
  mask_port = 255 /\ type_port = 222 /\ mask_code = 255 /\ type_code = 190 /\
  string_data_disp = 9 /\ vector_data_disp = 9 /\ bignum_data_disp = 9 /\ flonum_data_disp = 6 /\
  symbol_name_disp = 29 /\ closure_code_disp = 3 /\ closure_data_disp = 11 /\ code_data_disp = 65 /\
  string_length_offset = 4 /\ vector_length_offset = 4 /\ bignum_length_offset = 6 /\
  bignum_sign_offset = 5 /\ bigit_bits = 32 /\ bigit_bytes = 4 /\ string_char_bytes = 4.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------- memory and pointers *)

Definition mem := Z -> Z.                       (* byte at each address *)
Fixpoint load (m : mem) (a : Z) (n : nat) : Z := match n with
 | O => 0
 | S n => m a mod 256 + 256 * load m (a + 1) n end.  (* little endian *)
Definition load64 m a := load m a 8.
Definition load32 m a := load m a 4.

(* c/types.h: TYPE(x,t) = x - typemod + t; UNTYPE(x,t) = x + typemod - t. *)
Definition untag (t w : Z) : Z := w + typemod - t.
Definition ptag (w : Z) : Z := Z.land w (typemod - 1).
(* A pointer with primary tag t to an object at a nonzero, byte_alignment
   aligned address. *)
Definition ptr_ok (t w : Z) : Prop :=
  word_ok w /\ 0 < untag t w /\ untag t w mod byte_alignment = 0.

Lemma ptr_tag : forall t w, ptr_ok t w -> 0 <= t < typemod -> ptag w = t.
Proof.
  intros t w (Hw & Hp & Ha) Ht; unfold ptag, untag in *.
  destruct chez_object_layout as (HT & HB & _); rewrite HT, HB in *.
  apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k Hk].
  change (8 - 1) with (Z.ones 3); rewrite Z.land_ones by lia.
  symmetry; apply (Z.mod_unique _ _ (2 * k - 1)); [lia|]. change (2 ^ 3) with 8. lia.
Qed.

(* Every field at displacement disp of a t-tagged object, where
   disp + t - typemod is a multiple of ptr_bytes, is ptr_bytes aligned. *)
Theorem field_aligned : forall t w disp, ptr_ok t w ->
  (disp + t - typemod) mod ptr_bytes = 0 -> (w + disp) mod ptr_bytes = 0.
Proof.
  intros t w disp (Hw & Hp & Ha) Hd; unfold untag in *.
  unfold ptr_bytes, typemod, byte_alignment in *.
  apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k Hk].
  apply Z.mod_divide in Hd; [|lia]. destruct Hd as [j Hj].
  apply Z.mod_divide; [lia|]. exists (2 * k + j). lia.
Qed.

(* Ground derivation: every field the relation reads is 8-byte aligned. *)
Lemma chez_fields_aligned :
  (pair_car_disp + type_pair - typemod) mod ptr_bytes = 0 /\
  (pair_cdr_disp + type_pair - typemod) mod ptr_bytes = 0 /\
  (string_type_disp + type_typed_object - typemod) mod ptr_bytes = 0 /\
  (string_data_disp + type_typed_object - typemod) mod ptr_bytes = 0 /\
  (vector_data_disp + type_typed_object - typemod) mod ptr_bytes = 0 /\
  (bignum_data_disp + type_typed_object - typemod) mod ptr_bytes = 0 /\
  (flonum_data_disp + type_flonum - typemod) mod ptr_bytes = 0 /\
  (symbol_name_disp + type_symbol - typemod) mod ptr_bytes = 0 /\
  (closure_code_disp + type_closure - typemod) mod ptr_bytes = 0 /\
  (closure_data_disp + type_closure - typemod) mod ptr_bytes = 0 /\
  (code_data_disp + type_typed_object - typemod) mod byte_alignment = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------- object shapes *)

(* Strings: header = length << string_length_offset | type_string (bit 3 is
   the immutable flag, free here); elements are 32-bit string-chars, the low
   half of a Chez char: code << char_data_offset | type_char. Shen strings are
   code-point sequences (VALUE-MODEL); each element must be a Unicode scalar. *)
Fixpoint chars_at (m : mem) (a : Z) (t : text) : Prop := match t with
 | [] => True
 | c :: t => load32 m a = Z.of_N c * char_factor + type_char /\ scalar_ok (Z.of_N c) = true /\
             chars_at m (a + string_char_bytes) t end.
Definition string_at (m : mem) (w : Z) (t : text) : Prop :=
  ptr_ok type_typed_object w /\
  Z.land (load64 m (w + string_type_disp)) mask_string = type_string /\
  Z.shiftr (load64 m (w + string_type_disp)) string_length_offset = Z.of_nat (length t) /\
  chars_at m (w + string_data_disp) t.

(* Bignums: header = length << 6 | sign << 5 | type_bignum; 32-bit bigits,
   most significant first (c/number.c BIGIT(x,0)); value = sign * magnitude. *)
Fixpoint bigits (m : mem) (a : Z) (n : nat) : Z := match n with
 | O => 0
 | S k => load32 m a * 2 ^ (bigit_bits * Z.of_nat k) + bigits m (a + bigit_bytes) k end.
Definition bignum_value (m : mem) (w : Z) : Z :=
  let h := load64 m (w + bignum_type_disp) in
  let mag := bigits m (w + bignum_data_disp) (Z.to_nat (Z.shiftr h bignum_length_offset)) in
  if Z.testbit h bignum_sign_offset then - mag else mag.
Definition bignum_at (m : mem) (w z : Z) : Prop :=
  ptr_ok type_typed_object w /\
  Z.land (load64 m (w + bignum_type_disp)) mask_bignum = type_bignum /\ z = bignum_value m w.

Definition flonum_at (m : mem) (w : Z) (b : N) : Prop :=
  ptr_ok type_flonum w /\ load64 m (w + flonum_data_disp) = Z.of_N b.

Definition symbol_at (m : mem) (w : Z) (s : name) : Prop :=
  ptr_ok type_symbol w /\ string_at m (load64 m (w + symbol_name_disp)) s.

(* Closure: first word is the entry address = code object + code_data_disp
   (equates.h CLOSCODE). *)
Definition code_at (m : mem) (c : Z) : Prop :=
  ptr_ok type_typed_object c /\ Z.land (load64 m (c + code_type_disp)) mask_code = type_code.
Definition closure_at (m : mem) (w : Z) : Prop :=
  ptr_ok type_closure w /\ code_at m (load64 m (w + closure_code_disp) - code_data_disp).

Definition vector_hdr (m : mem) (w : Z) : Prop :=
  ptr_ok type_typed_object w /\ Z.land (load64 m (w + vector_type_disp)) mask_vector = type_vector.
Definition port_at (m : mem) (w : Z) : Prop :=
  ptr_ok type_typed_object w /\ Z.land (load64 m (w + port_type_disp)) mask_port = type_port.
Definition record_at (m : mem) (w : Z) : Prop :=
  ptr_ok type_typed_object w /\ Z.land (load64 m (w + record_type_disp)) mask_record = type_record.

Definition is_proc (v : value) : Prop := match v with
 | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => True | _ => False end.

(* ---------------------------------------------------------------- the relation *)

Section Rel.
Variable m : mem.
Variable loc : nat -> option Z.          (* address of each vector location *)
Variable proc : value -> Z -> Prop.      (* meaning of a closure word: E2E-22 *)
Variable port : N -> Z -> Prop.          (* meaning of a port word: E2E-27 *)
Variable cond : exn -> Z -> Prop.        (* meaning of a condition record: E2E-17/24 *)

Inductive rv : value -> Z -> Prop :=
 | RFix : forall z, fx_range z -> rv (VNum (NInt z)) (fx_enc z)
 | RBig : forall z w, ~ fx_range z -> bignum_at m w z -> rv (VNum (NInt z)) w
 | RFlo : forall b w, flonum_at m w b -> rv (VNum (NFloat b)) w
 | RTrue : rv (VBool true) strue
 | RFalse : rv (VBool false) sfalse
 | RNil : rv VNil snil
 | RSym : forall s w, symbol_at m w s -> rv (VSym s) w
 | RStr : forall t w, string_at m w t -> rv (VStr t) w
 | RCons : forall a d w, ptr_ok type_pair w ->
     rv a (load64 m (w + pair_car_disp)) -> rv d (load64 m (w + pair_cdr_disp)) -> rv (VCons a d) w
 | RVec : forall l w, loc l = Some w -> vector_hdr m w -> rv (VVec l) w
 | RProc : forall v w, is_proc v -> closure_at m w -> proc v w -> rv v w
 | RStream : forall h w, port_at m w -> port h w -> rv (VStream h) w
 | RExn : forall x w, record_at m w -> cond x w -> rv (VExn x) w.

(* Vector heap: each location's cells sit in a vector object at loc l, and
   distinct locations are distinct objects. *)
Definition vector_at (w : Z) (cells : list value) : Prop :=
  vector_hdr m w /\
  Z.shiftr (load64 m (w + vector_type_disp)) vector_length_offset = Z.of_nat (length cells) /\
  forall i v, nth_error cells i = Some v ->
    rv v (load64 m (w + vector_data_disp + ptr_bytes * Z.of_nat i)).
Definition loc_inj : Prop := forall l1 l2 w, loc l1 = Some w -> loc l2 = Some w -> l1 = l2.
Definition heap_rel (h : list (list value)) : Prop :=
  loc_inj /\ forall l cells, nth_error h l = Some cells -> exists w, loc l = Some w /\ vector_at w cells.

(* ---------------------------------------------------------------- tag decoding *)

Inductive kind := KFix | KBig | KFlo | KBool | KNil | KSym | KStr | KPair | KVec | KProc
 | KStream | KExn | KOther.

Definition vkind (v : value) : kind := match v with
 | VNum (NInt z) => if fx_rangeb z then KFix else KBig
 | VNum (NFloat _) => KFlo | VBool _ => KBool | VNil => KNil | VSym _ => KSym | VStr _ => KStr
 | VCons _ _ => KPair | VVec _ => KVec | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => KProc
 | VStream _ => KStream | VExn _ => KExn end.

(* A total decoder from a word (and the header word it points to) to a kind,
   written with the pinned constants only. *)
Definition classify (w : Z) : kind :=
  let t := ptag w in
  if t =? type_fixnum then KFix
  else if t =? type_pair then KPair
  else if t =? type_flonum then KFlo
  else if t =? type_symbol then KSym
  else if t =? type_closure then KProc
  else if t =? type_immediate then
    (if w =? snil then KNil else if (w =? strue) || (w =? sfalse) then KBool else KOther)
  else if t =? type_typed_object then
    (let h := load64 m (w + 1) in
     if Z.land h mask_vector =? type_vector then KVec
     else if Z.land h mask_string =? type_string then KStr
     else if Z.land h mask_record =? type_record then KExn
     else if Z.land h mask_bignum =? type_bignum then KBig
     else if Z.land h mask_port =? type_port then KStream
     else KOther)
  else KOther.

Lemma land_sub : forall h m1 m2 t1, Z.land h m1 = t1 -> Z.land m1 m2 = m2 -> Z.land h m2 = Z.land t1 m2.
Proof. intros h m1 m2 t1 H1 H2; rewrite <- H1, <- Z.land_assoc, H2; reflexivity. Qed.

Ltac layout := destruct chez_object_layout as
  (HTM & HBA & HTP & HTF & HTS & HTC & HTI & HTT & HST & HSF & HSN & HSV & HSU & HSE & HSB &
   HBH & HFM & HTCH & HCF & HCAR & HCDR & HDS & HDV & HDB & HDR & HDP & HDC & HMS & HTSt &
   HMV & HTV & HMB & HTB & HMR & HTR & HMP & HTPo & HMC & HTCo & _).

Lemma ptr_ptag : forall t w, ptr_ok t w -> 0 <= t < typemod -> ptag w = t.
Proof. exact ptr_tag. Qed.

Lemma fix_ptag : forall z, ptag (fx_enc z) = type_fixnum.
Proof.
  intro z; pose proof (fx_enc_tagged z) as H; unfold fixnum_tagged in H; unfold ptag.
  destruct chez_fixnum_layout as (_ & _ & _ & _ & _ & _ & HM & _); rewrite <- HM; exact H.
Qed.

Theorem rv_classify : forall v w, rv v w -> classify w = vkind v.
Proof.
  intros v w H; destruct H; unfold classify, vkind.
  - rewrite fix_ptag, Z.eqb_refl. apply fx_rangeb_spec in H; rewrite H; reflexivity.
  - destruct H0 as (P & Hh & _). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTT; lia).
    rewrite HTT, HTP, HTF, HTS, HTC, HTI; cbn - [Z.land load64].
    rewrite HDB in Hh. rewrite HMB, HTB in Hh. rewrite HMV, HTV, HMS, HTSt, HMR, HTR, HMB, HTB.
    rewrite (land_sub _ 31 7 6 Hh eq_refl), Hh; cbn.
    destruct (fx_rangeb z) eqn:E; [apply fx_rangeb_spec in E; contradiction|reflexivity].
  - destruct H as (P & _). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTF; lia). rewrite HTF, HTP; reflexivity.
  - layout. rewrite HST; reflexivity.
  - layout. rewrite HSF; reflexivity.
  - layout. rewrite HSN; reflexivity.
  - destruct H as (P & _). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTS; lia). rewrite HTS, HTP, HTF; reflexivity.
  - destruct H as (P & Hh & _). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTT; lia).
    rewrite HTT, HTP, HTF, HTS, HTC, HTI; cbn - [Z.land load64].
    rewrite HDS, HMS, HTSt in Hh. rewrite HMV, HTV, HMS, HTSt, Hh; reflexivity.
  - layout. rewrite (ptr_ptag _ _ H) by (rewrite HTM, HTP; lia). rewrite HTP; reflexivity.
  - destruct H0 as (P & Hh). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTT; lia).
    rewrite HTT, HTP, HTF, HTS, HTC, HTI; cbn - [Z.land load64].
    rewrite HDV, HMV, HTV in Hh. rewrite HMV, HTV, Hh; reflexivity.
  - destruct H0 as (P & _). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTC; lia).
    rewrite HTC, HTP, HTF, HTS. destruct v; cbn in H; try contradiction; reflexivity.
  - destruct H as (P & Hh). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTT; lia).
    rewrite HTT, HTP, HTF, HTS, HTC, HTI; cbn - [Z.land load64].
    rewrite HDP, HMP, HTPo in Hh. rewrite HMV, HTV, HMS, HTSt, HMR, HTR, HMB, HTB, HMP, HTPo.
    rewrite (land_sub _ 255 7 222 Hh eq_refl), (land_sub _ 255 31 222 Hh eq_refl), Hh; reflexivity.
  - destruct H as (P & Hh). layout.
    rewrite (ptr_ptag _ _ P) by (rewrite HTM, HTT; lia).
    rewrite HTT, HTP, HTF, HTS, HTC, HTI; cbn - [Z.land load64].
    rewrite HDR, HMR, HTR in Hh. rewrite HMV, HTV, HMS, HTSt, HMR, HTR, Hh; reflexivity.
Qed.

(* Tag decoding is injective on kinds: one word never represents values of
   two different kinds (fixnum vs bignum, boolean vs nil vs symbol, string vs
   vector vs bignum vs port vs condition, ...). *)
Theorem rv_kind_unique : forall v1 v2 w, rv v1 w -> rv v2 w -> vkind v1 = vkind v2.
Proof. intros v1 v2 w H1 H2; rewrite <- (rv_classify _ _ H1), <- (rv_classify _ _ H2); reflexivity. Qed.

(* Chez immediates outside the Shen value space: no Shen value is represented
   by #!void (the value a Shen-Scheme `cond` with no true clause returns,
   VALUE-MODEL), #!unbound, #!eof, #!bwp, the black hole or the forward marker. *)
Theorem non_values_unrepresented : forall v,
  ~ rv v svoid /\ ~ rv v sunbound /\ ~ rv v seof /\ ~ rv v sbwp /\ ~ rv v black_hole /\
  ~ rv v forward_marker.
Proof.
  intro v.
  assert (C : forall w, In w [svoid; sunbound; seof; sbwp; black_hole; forward_marker] ->
               classify w = KOther) by (intros w Hw; cbn in Hw; vm_compute in Hw;
               repeat destruct Hw as [<-|Hw]; try contradiction; reflexivity).
  assert (K : forall w, In w [svoid; sunbound; seof; sbwp; black_hole; forward_marker] -> ~ rv v w).
  { intros w Hw R; pose proof (rv_classify _ _ R) as E; rewrite (C w Hw) in E.
    destruct v as [[]| | | | | | | | | | |]; cbn in E; try discriminate.
    destruct (fx_rangeb z); discriminate. }
  repeat split; apply K; cbn; tauto.
Qed.

(* Immediates and pointers are disjoint, and fixnums are neither. *)
Theorem immediate_pointer_disjoint : forall t w, ptr_ok t w ->
  In t [type_pair; type_flonum; type_symbol; type_closure; type_typed_object] ->
  ptag w <> type_immediate /\ ptag w <> type_fixnum /\
  w <> strue /\ w <> sfalse /\ w <> snil /\ (forall z, w <> fx_enc z).
Proof.
  intros t w P Ht.
  assert (Ht' : 0 <= t < typemod /\ t <> type_immediate /\ t <> type_fixnum).
  { cbn in Ht; vm_compute in Ht; vm_compute; repeat destruct Ht as [<-|Ht]; try contradiction;
    repeat split; discriminate. }
  destruct Ht' as (R & N1 & N2).
  pose proof (ptr_ptag _ _ P R) as E; rewrite E.
  repeat split; try assumption.
  - intro X; subst w; vm_compute in E; subst t; vm_compute in N1; congruence.
  - intro X; subst w; vm_compute in E; subst t; vm_compute in N1; congruence.
  - intro X; subst w; vm_compute in E; subst t; vm_compute in N1; congruence.
  - intros z X; subst w; rewrite fix_ptag in E; congruence.
Qed.

(* ---------------------------------------------------------------- decoding is a function *)

(* First-order data: no procedure, stream or exception inside. *)
Fixpoint fo (v : value) : Prop := match v with
 | VCons a d => fo a /\ fo d
 | VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VStream _ | VExn _ => False
 | _ => True end.

Lemma chars_at_functional : forall a t1 t2, chars_at m a t1 -> chars_at m a t2 ->
  length t1 = length t2 -> t1 = t2.
Proof.
  intros a t1; revert a; induction t1 as [|c t1 IH]; intros a [|d t2] H1 H2 L; cbn in *;
    try discriminate; auto.
  destruct H1 as (E1 & _ & R1), H2 as (E2 & _ & R2).
  rewrite E1 in E2. layout. rewrite HCF, HTCH in E2.
  assert (c = d) by lia. subst d. f_equal. apply (IH _ _ R1 R2). lia.
Qed.

Lemma string_at_functional : forall w t1 t2, string_at m w t1 -> string_at m w t2 -> t1 = t2.
Proof.
  intros w t1 t2 (_ & _ & L1 & C1) (_ & _ & L2 & C2).
  apply (chars_at_functional _ _ _ C1 C2). rewrite L1 in L2. lia.
Qed.

Lemma fx_rangeb_false : forall z, ~ fx_range z -> fx_rangeb z = false.
Proof. intros z H; destruct (fx_rangeb z) eqn:E; [apply fx_rangeb_spec in E; contradiction|reflexivity]. Qed.

Ltac fxb := repeat match goal with
 | H : fx_range ?z, K : context [fx_rangeb ?z] |- _ => rewrite (proj2 (fx_rangeb_spec z) H) in K
 | H : ~ fx_range ?z, K : context [fx_rangeb ?z] |- _ => rewrite (fx_rangeb_false z H) in K
 end.

Theorem rv_functional : loc_inj -> forall v1 w, rv v1 w -> fo v1 -> forall v2, rv v2 w -> v1 = v2.
Proof.
  intros LI v1 w H1. assert (K1 := rv_classify _ _ H1). revert K1.
  induction H1; intros K1 F v2 H2; assert (K2 := rv_classify _ _ H2); rewrite K1 in K2;
    try (match goal with Hp : is_proc ?v, Fp : fo ?v |- _ => destruct v; cbn in Hp, Fp; contradiction end);
    try (cbn in F; contradiction);
    inversion H2; subst; cbn in K2; fxb;
    try (match goal with Hp : is_proc ?v |- _ => destruct v; cbn in Hp, K2; fxb; try contradiction; try discriminate;
           try (destruct (fx_rangeb _); discriminate) end);
    try discriminate; try reflexivity.
  - f_equal; f_equal; apply fx_enc_inj; auto.
  - match goal with A : bignum_at _ _ _, B : bignum_at _ _ _ |- _ =>
      destruct A as (_ & _ & E1), B as (_ & _ & E2) end. rewrite E1, E2; reflexivity.
  - match goal with A : flonum_at _ _ _, B : flonum_at _ _ _ |- _ =>
      destruct A as (_ & E1), B as (_ & E2) end. rewrite E1 in E2. apply N2Z.inj in E2. subst; reflexivity.
  - match goal with A : symbol_at _ _ _, B : symbol_at _ _ _ |- _ =>
      destruct A as (_ & S1), B as (_ & S2) end. f_equal. apply (string_at_functional _ _ _ S1 S2).
  - f_equal. eapply string_at_functional; eassumption.
  - destruct F as (Fa & Fd). f_equal; [apply IHrv1|apply IHrv2]; auto using rv_classify.
  - f_equal. eapply LI; eassumption.
Qed.

(* ---------------------------------------------------------------- machine operations *)

Theorem car_cdr_repr : forall a d w, rv (VCons a d) w ->
  ptr_ok type_pair w /\ rv a (load64 m (w + pair_car_disp)) /\ rv d (load64 m (w + pair_cdr_disp)) /\
  (w + pair_car_disp) mod ptr_bytes = 0 /\ (w + pair_cdr_disp) mod ptr_bytes = 0.
Proof.
  intros a d w H; inversion H; subst; [|cbn in *; contradiction].
  destruct chez_fields_aligned as (A1 & A2 & _).
  refine (conj H2 (conj H3 (conj H5 (conj _ _)))); apply (field_aligned type_pair); assumption.
Qed.

Lemma chars_at_nth : forall t a i c, chars_at m a t -> nth_error t i = Some c ->
  load32 m (a + string_char_bytes * Z.of_nat i) = Z.of_N c * char_factor + type_char /\
  Z.shiftr (load32 m (a + string_char_bytes * Z.of_nat i)) char_data_offset = Z.of_N c.
Proof.
  induction t as [|d t IH]; intros a [|i] c H E; simpl nth_error in E; try discriminate.
  - inversion E; subst. destruct H as (L & _). change (Z.of_nat 0) with 0.
    rewrite Z.mul_0_r, Z.add_0_r, L. split; [reflexivity|].
    layout. rewrite HCF, HTCH. change char_data_offset with 8.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.div_add_l by lia. change (22 / 256) with 0. lia.
  - destruct H as (_ & _ & R). destruct (IH _ i c R E) as [A B].
    replace (a + string_char_bytes * Z.of_nat (S i))
      with (a + string_char_bytes + string_char_bytes * Z.of_nat i) by lia.
    split; assumption.
Qed.

(* string-ref and string-length on the representation compute the Shen
   string's code points and length. *)
Theorem string_ref_repr : forall t w i c, rv (VStr t) w -> nth_error t i = Some c ->
  Z.shiftr (load32 m (w + string_data_disp + string_char_bytes * Z.of_nat i)) char_data_offset = Z.of_N c.
Proof.
  intros t w i c H E; inversion H; subst; [|cbn in *; contradiction].
  destruct H1 as (_ & _ & _ & C). apply (chars_at_nth _ _ _ _ C E).
Qed.

Theorem string_length_repr : forall t w, rv (VStr t) w ->
  Z.shiftr (load64 m (w + string_type_disp)) string_length_offset = Z.of_nat (length t).
Proof. intros t w H; inversion H; subst; [destruct H1 as (_ & _ & L & _); exact L|cbn in *; contradiction]. Qed.

(* vector-ref and vector-length on the representation read the abstract heap. *)
Theorem vector_ref_repr : forall h l w cells i v, heap_rel h -> rv (VVec l) w ->
  nth_error h l = Some cells -> nth_error cells i = Some v ->
  rv v (load64 m (w + vector_data_disp + ptr_bytes * Z.of_nat i)) /\
  Z.shiftr (load64 m (w + vector_type_disp)) vector_length_offset = Z.of_nat (length cells).
Proof.
  intros h l w cells i v (LI & HR) R E1 E2.
  inversion R; subst; [|cbn in *; contradiction].
  destruct (HR _ _ E1) as (w' & L' & (_ & Len & Cells)).
  match goal with Hl : loc l = Some w |- _ => rewrite Hl in L' end.
  inversion L'; subst. split; [apply Cells; assumption|assumption].
Qed.

Theorem heap_rel_vec : forall h (l : nat), heap_rel h -> (l < length h)%nat -> exists w, rv (VVec l) w.
Proof.
  intros h l (_ & HR) Lt. destruct (nth_error h l) as [cells|] eqn:E.
  - destruct (HR _ _ E) as (w & L & (V & _)). exists w. constructor; assumption.
  - apply nth_error_None in E; lia.
Qed.

(* ---------------------------------------------------------------- the ARM fast path *)

(* The premises of the Islaris theorem buri_chez_add_fast_path
   (ports/arm/islaris/buri_chez_add.v) as consequences of "X0 and X1
   represent Shen integers x and y": the tag test (a|b)&7 = 0 holds exactly
   when both are fixnums; then the signed-overflow premise holds exactly when
   x + y is a fixnum, and the result word a + b represents x + y. A bignum
   operand makes the tag test fail (slow path, library `+`, E2E-24). *)
Theorem shen_int_tag_test : forall x y a b, rv (VNum (NInt x)) a -> rv (VNum (NInt y)) b ->
  (Z.land (Z.lor a b) mask_fixnum = 0 <-> fx_range x /\ fx_range y).
Proof.
  assert (T : forall z w, rv (VNum (NInt z)) w -> (fixnum_tagged w <-> fx_range z)).
  { intros z w R; inversion R; subst.
    - split; [intros _; assumption|intros _; apply fx_enc_tagged].
    - split; [|intro; contradiction]. intro X. exfalso.
      destruct H1 as (P & _). layout.
      pose proof (ptr_ptag _ _ P ltac:(rewrite HTM, HTT; lia)) as E.
      unfold fixnum_tagged, ptag in *. destruct chez_fixnum_layout as (_ & _ & _ & _ & _ & _ & HM & HZ & _).
      rewrite HM, E in X. rewrite HTT, HZ in X. discriminate.
    - cbn in *; contradiction. }
  intros x y a b Ra Rb. rewrite tag_or_iff, (T _ _ Ra), (T _ _ Rb). tauto.
Qed.

Lemma rv_fix_word : forall z w, rv (VNum (NInt z)) w -> fx_range z -> w = fx_enc z.
Proof.
  intros z w R F; inversion R; subst; [reflexivity|contradiction|cbn in *; contradiction].
Qed.

Theorem shen_int_add_fast_path : forall x y a b,
  rv (VNum (NInt x)) a -> rv (VNum (NInt y)) b -> Z.land (Z.lor a b) mask_fixnum = 0 ->
  a = fx_enc x /\ b = fx_enc y /\
  (- half <= swrap a + swrap b < half <-> fx_range (x + y)) /\
  (fx_range (x + y) -> rv (VNum (NInt (x + y))) (wrap (a + b))).
Proof.
  intros x y a b Ra Rb T. apply (shen_int_tag_test _ _ _ _ Ra Rb) in T. destruct T as [Fx Fy].
  rewrite (rv_fix_word _ _ Ra Fx), (rv_fix_word _ _ Rb Fy).
  split; [reflexivity|]. split; [reflexivity|]. split; [apply fx_add_no_overflow_iff; assumption|].
  intro S; rewrite fx_add_wrap; constructor; exact S.
Qed.

End Rel.

(* ---------------------------------------------------------------- sampled agreement *)

(* Sampled agreement (one emulated tarm64le process, ports/repr/chez/
   chez-10.3.0-tarm64le-sample.capture): the words read from live objects
   equal the encodings defined above. This is a ground check of one sample,
   not evidence for the relation in general. *)
Lemma chez_sample_agrees :
  sample_machine_type_tarm64le = 1 /\ sample_fixnum_width = fixnum_bits /\
  sample_most_positive_fixnum = most_positive_fixnum /\
  sample_most_negative_fixnum = most_negative_fixnum /\
  sample_pair_car_word = fx_enc 1 /\ sample_pair_cdr_word = fx_enc (-2) /\
  sample_vector_header = Z.shiftl 5 vector_length_offset + type_mutable_vector /\
  sample_vector_elt0_true = strue /\ sample_vector_elt1_false = sfalse /\
  sample_vector_elt2_nil = snil /\ sample_vector_elt3_void = svoid /\
  sample_vector_elt4_fixnum5 = fx_enc 5 /\
  sample_string_header = Z.shiftl 2 string_length_offset + type_mutable_string /\
  sample_string_char0 = 97 * char_factor + type_char /\
  sample_string_char1 = 955 * char_factor + type_char /\
  sample_bignum_header = Z.shiftl 3 bignum_length_offset + type_positive_bignum /\
  sample_bignum_bigit0 * 2 ^ (2 * bigit_bits) + sample_bignum_bigit1 * 2 ^ bigit_bits
    + sample_bignum_bigit2 = 2 ^ 70 /\
  sample_flonum_bits = 4609434218613702656 /\
  sample_symbol_name_is_string = 1 /\ sample_closure_code_is_code = 1 /\
  sample_closure_free0 = fx_enc 1 /\
  sample_closure_entry_minus_code = code_data_disp /\
  sample_closure_entry_mod16 = (code_data_disp + type_typed_object - typemod) mod byte_alignment /\
  sample_pair_ptr_mod16 = (type_pair - typemod) mod byte_alignment /\
  sample_flonum_ptr_mod16 = (type_flonum - typemod) mod byte_alignment /\
  sample_symbol_ptr_mod16 = (type_symbol - typemod) mod byte_alignment /\
  sample_closure_ptr_mod16 = (type_closure - typemod) mod byte_alignment /\
  sample_string_ptr_mod16 = (type_typed_object - typemod) mod byte_alignment /\
  sample_vector_ptr_mod16 = (type_typed_object - typemod) mod byte_alignment /\
  sample_bignum_ptr_mod16 = (type_typed_object - typemod) mod byte_alignment.
Proof. vm_compute. repeat split; reflexivity. Qed.

End ChezRepr.
