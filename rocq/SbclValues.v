(* E2E-21 (CL side): representation relation between KLambda values
   (KLValue) and SBCL 2.6.8 arm64 machine words and memory, for Shen-CL.

   Scope (stated precisely; see docs/REPRESENTATION.md section 5):
   * one memory snapshot [m] (bytes, little endian), a vector-location map
     [loc] and a symbol table [symw] (the word of the interned SHEN-package
     symbol of each Shen name); nothing here is about how the snapshot
     changes (allocation, GC moves, mutation, threads: E2E-25/E2E-28);
   * procedures, streams and exception objects are related through the
     parameters [proc], [port], [cond], whose meaning is owed by E2E-22,
     E2E-27 and E2E-17/24; the relation fixes only their machine shape;
   * every layout number is an SbclLayout constant (generated from the
     pinned sources and image); the NIL layout is genesis.lisp's
     (SbclTests.sbcl_source_flags).
   Shen-CL represents Shen's booleans as the symbols true and false and
   Shen's [] as CL NIL. So one word represents both VBool true and
   VSym "true" ([kl_bool_symbol_collision]): unlike the Chez relation this
   one is not a function from words to values, and NIL is at once the empty
   list, CL false and a symbol ([nil_dual], [kl_symbolp_test]).

   This is a relation about the reference representation of Shen-CL on
   SBCL 2.6.8 arm64. It is not a theorem that Shen-CL preserves it. *)
From Coq Require Import ZArith List Lia Bool.
From Buri Require Import Observation KLSyntax KLValue SbclLayout SbclWord SbclA64 SbclTests.
Import ListNotations.
Open Scope Z_scope.
Module SbclValues.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue SbclLayout.SbclLayout
  SbclWord.SbclWord SbclA64.SbclA64 SbclTests.SbclTests.

(* ---------------------------------------------------------------- ground layout *)

Lemma sbcl_object_layout :
  img_instance_pointer_lowtag = 3 /\ img_list_pointer_lowtag = 7 /\ img_fun_pointer_lowtag = 11 /\
  img_other_pointer_lowtag = 15 /\ img_bignum_widetag = 17 /\ img_double_float_widetag = 29 /\
  img_symbol_widetag = 45 /\ img_simple_vector_widetag = 137 /\ img_simple_base_string_widetag = 225 /\
  img_simple_character_string_widetag = 229 /\ img_instance_widetag = 57 /\ img_simple_fun_widetag = 65 /\
  img_closure_widetag = 69 /\ img_funcallable_instance_widetag = 61 /\ img_character_widetag = 81 /\
  img_single_float_widetag = 25 /\ img_cons_car_slot = 0 /\ img_cons_cdr_slot = 1 /\
  img_vector_length_slot = 1 /\ img_vector_data_offset = 2 /\ img_double_float_value_slot = 1 /\
  img_bignum_digits_offset = 1 /\ img_n_word_bytes = 8 /\ img_n_widetag_bits = 8 /\
  nilv = img_nil_value /\ src_symbol_widetag = img_symbol_widetag.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------- memory and objects *)

Definition mem := Z -> Z.
Fixpoint load (m : mem) (a : Z) (n : nat) : Z := match n with
 | O => 0
 | S n => m a mod 256 + 256 * load m (a + 1) n end.
Definition load64 m a := load m a 8.
Definition load32 m a := load m a 4.

(* A lowtag-t pointer to a 16-byte aligned object at a positive address. *)
Definition ptr_ok (t w : Z) : Prop := word_ok w /\ lowtag w = t /\ t < w.
(* Slot i of a lowtag-t object: the word at w - t + 8 i (objdef.lisp). *)
Definition slot (m : mem) (t w i : Z) : Z := load64 m (w - t + img_n_word_bytes * i).
Definition widetag_at (m : mem) (t w : Z) : Z := m (w - t) mod 256.
Definition other_at (m : mem) (w wt : Z) : Prop :=
  ptr_ok img_other_pointer_lowtag w /\ widetag_at m img_other_pointer_lowtag w = wt.

Fixpoint chars32 (m : mem) (a : Z) (t : text) : Prop := match t with
 | [] => True
 | c :: t => load32 m a = Z.of_N c /\ chars32 m (a + 4) t end.
Fixpoint chars8 (m : mem) (a : Z) (t : text) : Prop := match t with
 | [] => True
 | c :: t => m a mod 256 = Z.of_N c /\ Z.of_N c < 128 /\ chars8 m (a + 1) t end.
(* A simple-character-string (32-bit code points) or a simple-base-string
   (bytes, base-char codes < 128); the length slot holds a fixnum. *)
Definition string_at (m : mem) (w : Z) (t : text) : Prop :=
  fx_range (Z.of_nat (length t)) /\
  slot m img_other_pointer_lowtag w img_vector_length_slot = fx_enc (Z.of_nat (length t)) /\
  ((other_at m w img_simple_character_string_widetag /\
    chars32 m (w - img_other_pointer_lowtag + img_n_word_bytes * img_vector_data_offset) t) \/
   (other_at m w img_simple_base_string_widetag /\
    chars8 m (w - img_other_pointer_lowtag + img_n_word_bytes * img_vector_data_offset) t)).

(* Bignums: header length (words) above the widetag byte; digits are 64-bit
   words from slot 1, least significant first, two's complement. *)
Fixpoint digits (m : mem) (a : Z) (n : nat) : Z := match n with
 | O => 0
 | S k => load64 m a + 2 ^ 64 * digits m (a + 8) k end.
Definition bignum_len (m : mem) (w : Z) : Z := Z.shiftr (slot m img_other_pointer_lowtag w 0) img_n_widetag_bits.
Definition bignum_value (m : mem) (w : Z) : Z :=
  let n := Z.to_nat (bignum_len m w) in
  let u := digits m (w - img_other_pointer_lowtag + img_n_word_bytes * img_bignum_digits_offset) n in
  if u <? 2 ^ (64 * Z.of_nat n - 1) then u else u - 2 ^ (64 * Z.of_nat n).
Definition bignum_at (m : mem) (w z : Z) : Prop :=
  other_at m w img_bignum_widetag /\ 1 <= bignum_len m w /\ z = bignum_value m w.
Definition double_at (m : mem) (w : Z) (b : N) : Prop :=
  other_at m w img_double_float_widetag /\
  slot m img_other_pointer_lowtag w img_double_float_value_slot = Z.of_N b.
Definition symbol_at (m : mem) (w : Z) : Prop := other_at m w img_symbol_widetag.
Definition vector_hdr (m : mem) (w : Z) : Prop := other_at m w img_simple_vector_widetag.
Definition fun_at (m : mem) (w : Z) : Prop :=
  ptr_ok img_fun_pointer_lowtag w /\
  In (widetag_at m img_fun_pointer_lowtag w)
     [img_simple_fun_widetag; img_closure_widetag; img_funcallable_instance_widetag].
Definition instance_at (m : mem) (w : Z) : Prop :=
  ptr_ok img_instance_pointer_lowtag w /\ widetag_at m img_instance_pointer_lowtag w = img_instance_widetag.
Definition cons_ok (w : Z) : Prop := ptr_ok img_list_pointer_lowtag w /\ w <> nilv.
Definition car_w (m : mem) (w : Z) := slot m img_list_pointer_lowtag w img_cons_car_slot.
Definition cdr_w (m : mem) (w : Z) := slot m img_list_pointer_lowtag w img_cons_cdr_slot.

(* genesis.lisp: NIL viewed as a cons has car and cdr NIL, and the byte read
   through the other-pointer view (NIL - 15) is symbol-widetag. *)
Definition nil_layout (m : mem) : Prop :=
  car_w m nilv = nilv /\ cdr_w m nilv = nilv /\ widetag_at m img_other_pointer_lowtag nilv = img_symbol_widetag.

Definition is_proc (v : value) : Prop := match v with
 | VLam _ _ _ | VFrozen _ _ | VPartial _ _ => True | _ => False end.

(* ---------------------------------------------------------------- the relation *)

Section Rel.
Variable m : mem.
Variable loc : nat -> option Z.          (* address of each vector location *)
Variable symw : name -> option Z.        (* interned symbol of each Shen name *)
Variable proc : value -> Z -> Prop.      (* meaning of a function object: E2E-22 *)
Variable port : N -> Z -> Prop.          (* meaning of a stream object: E2E-27 *)
Variable cond : exn -> Z -> Prop.        (* meaning of a condition object: E2E-17/24 *)

Inductive kv : value -> Z -> Prop :=
 | KFix : forall z, fx_range z -> kv (VNum (NInt z)) (fx_enc z)
 | KBig : forall z w, ~ fx_range z -> bignum_at m w z -> kv (VNum (NInt z)) w
 | KFlo : forall b w, double_at m w b -> kv (VNum (NFloat b)) w
 | KBool : forall b w, symw (bool_text b) = Some w -> symbol_at m w -> kv (VBool b) w
 | KNil : kv VNil nilv
 | KSym : forall s w, symw s = Some w -> symbol_at m w -> kv (VSym s) w
 | KStr : forall t w, string_at m w t -> forallb (fun c => scalar_ok (Z.of_N c)) t = true -> kv (VStr t) w
 | KCons : forall a d w, cons_ok w -> kv a (car_w m w) -> kv d (cdr_w m w) -> kv (VCons a d) w
 | KVec : forall l w, loc l = Some w -> vector_hdr m w -> kv (VVec l) w
 | KProc : forall v w, is_proc v -> fun_at m w -> proc v w -> kv v w
 | KStream : forall h w, instance_at m w -> port h w -> kv (VStream h) w
 | KExn : forall x w, instance_at m w -> cond x w -> kv (VExn x) w.

(* Vector heap: each location's cells sit in a simple-vector at loc l. *)
Definition vector_at (w : Z) (cells : list value) : Prop :=
  vector_hdr m w /\
  slot m img_other_pointer_lowtag w img_vector_length_slot = fx_enc (Z.of_nat (length cells)) /\
  forall i v, nth_error cells i = Some v ->
    kv v (slot m img_other_pointer_lowtag w (img_vector_data_offset + Z.of_nat i)).
Definition loc_inj : Prop := forall l1 l2 w, loc l1 = Some w -> loc l2 = Some w -> l1 = l2.
Definition heap_rel (h : list (list value)) : Prop :=
  loc_inj /\ forall l cells, nth_error h l = Some cells -> exists w, loc l = Some w /\ vector_at w cells.

(* ---------------------------------------------------------------- word facts *)

Lemma ptr_word : forall t w, ptr_ok t w -> 0 <= w < 2 ^ 64.
Proof. intros t w (W & _); destruct sbcl_word_layout as (_ & HM & _); unfold word_ok in W; rewrite HM in W; exact W. Qed.

Lemma lowtag_land : forall w, lowtag w = Z.land w 15.
Proof. intro w. unfold lowtag. destruct sbcl_word_layout as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _). rewrite HL. reflexivity. Qed.

Lemma odd_lowtag_bit0 : forall w, Z.testbit (lowtag w) 0 = true -> Z.testbit w 0 = true.
Proof.
  intros w H. rewrite lowtag_land in H. rewrite Z.land_spec in H. apply andb_true_iff in H. tauto.
Qed.

Lemma ptr_odd : forall t w, ptr_ok t w -> In t [3; 7; 11; 15] -> Z.testbit w 0 = true.
Proof.
  intros t w (_ & L & _) I. apply odd_lowtag_bit0. rewrite L.
  cbn in I. repeat destruct I as [<-|I]; try contradiction; reflexivity.
Qed.

Lemma trunc32_lowtag : forall w, trunc 32 w mod 16 = lowtag w.
Proof.
  intro w. rewrite lowtag_mod. unfold trunc.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia | exists (2 ^ 28); reflexivity].
Qed.

(* No pointer is a single-float immediate (low 32 bits 25 = lowtag 9). *)
Lemma ptr_not_single : forall t w, ptr_ok t w -> In t [3; 7; 11; 15] -> (trunc 32 w =? 25) = false.
Proof.
  intros t w (_ & L & _) I. apply Z.eqb_neq. intro E.
  pose proof (trunc32_lowtag w) as T. rewrite E, L in T. cbn in T.
  cbn in I. repeat destruct I as [<-|I]; try contradiction; discriminate.
Qed.

Lemma hdr_other : forall m' w, ptr_ok img_other_pointer_lowtag w -> hdr m' w = widetag_at m' img_other_pointer_lowtag w.
Proof.
  intros m' w P. pose proof (ptr_word _ _ P) as W. destruct P as (_ & _ & G). unfold hdr, widetag_at.
  change img_other_pointer_lowtag with 15 in *.
  rewrite (trunc_small 64 (w + -15)) by lia. reflexivity.
Qed.

Lemma nilv_lowtag : lowtag nilv = img_list_pointer_lowtag.
Proof. vm_compute. reflexivity. Qed.

Lemma ptr_ne_nil : forall t w, ptr_ok t w -> t <> img_list_pointer_lowtag -> w <> nilv.
Proof. intros t w (_ & L & _) N E. subst w. rewrite nilv_lowtag in L. congruence. Qed.

Lemma lowtag_eqb : forall t w, ptr_ok t w -> (Z.land w 15 =? 15) = (t =? 15) /\ (Z.land w 15 =? 7) = (t =? 7).
Proof. intros t w (_ & L & _). rewrite lowtag_land in L. rewrite L. split; reflexivity. Qed.

(* ---------------------------------------------------------------- NIL *)

(* NIL is a list pointer whose symbol descriptor (genesis nil-val = des + 8)
   is an other pointer; as a cons its car and cdr are NIL; the header byte
   the generic symbol test would read through NIL - 15 is symbol-widetag.
   The captured CONSP excludes it, and SYMBOLP special-cases it (the generic
   other-pointer test fails on lowtag 7). *)
Theorem nil_dual : nil_layout m ->
  lowtag nilv = img_list_pointer_lowtag /\ lowtag (nilv - 8) = img_other_pointer_lowtag /\
  car_w m nilv = nilv /\ cdr_w m nilv = nilv /\ hdr m nilv = img_symbol_widetag /\
  t_consp nilv = false /\ t_symbolp m nilv = true /\ t_null nilv = true /\
  ((Z.land nilv 15 =? 15) && (hdr m nilv =? img_symbol_widetag)) = false.
Proof.
  intros (A & D & H). split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [exact A|]. split; [exact D|].
  split. { unfold hdr, widetag_at in *. rewrite <- H. reflexivity. }
  vm_compute. repeat split; reflexivity.
Qed.

(* ---------------------------------------------------------------- the tests on values *)

Definition kl_cons (v : value) : bool := match v with VCons _ _ => true | _ => false end.
Definition kl_nil (v : value) : bool := match v with VNil => true | _ => false end.
(* CL SYMBOLP: Shen symbols, both booleans (symbols true/false) and [] (NIL). *)
Definition kl_cl_symbol (v : value) : bool := match v with VSym _ | VBool _ | VNil => true | _ => false end.
Definition kl_str (v : value) : bool := match v with VStr _ => true | _ => false end.
Definition kl_num (v : value) : bool := match v with VNum _ => true | _ => false end.
Definition kl_int (v : value) : bool := match v with VNum (NInt _) => true | _ => false end.
Definition kl_fixnum (v : value) : bool := match v with VNum (NInt z) => fx_rangeb z | _ => false end.
Definition kl_array (v : value) : bool := match v with VStr _ | VVec _ => true | _ => false end.

Ltac lay := pose proof sbcl_object_layout as (HL3 & HL7 & HL11 & HL15 & HWB & HWD & HWS & HWV & HWBS & HWCS &
  HWI & HWSF & HWC & HWFI & HWCh & HWSg & _).

(* Word facts of each constructor. *)
Inductive wshape : Z -> Prop :=
 | WFix : forall z, wshape (fx_enc z)
 | WOther : forall w wt, other_at m w wt -> In wt [17; 29; 45; 137; 225; 229] -> wshape w
 | WList : forall w, cons_ok w -> wshape w
 | WNil : wshape nilv
 | WFun : forall w, ptr_ok 11 w -> wshape w
 | WInst : forall w, ptr_ok 3 w -> wshape w.

Lemma string_other : forall w t, string_at m w t ->
  exists wt, other_at m w wt /\ (wt = 225 \/ wt = 229).
Proof. intros w t (_ & _ & [[O _]|[O _]]); lay; eexists; split; eauto; rewrite ?HWBS, ?HWCS in *; auto. Qed.

Lemma chars32_functional : forall a t1 t2, chars32 m a t1 -> chars32 m a t2 -> length t1 = length t2 -> t1 = t2.
Proof.
  intros a t1; revert a; induction t1 as [|c t1 IH]; intros a [|d t2] H1 H2 L; cbn in *; try discriminate; auto.
  destruct H1 as (E1 & R1), H2 as (E2 & R2). rewrite E1 in E2. apply N2Z.inj in E2. subst d.
  f_equal. apply (IH _ _ R1 R2). lia.
Qed.
Lemma chars8_functional : forall a t1 t2, chars8 m a t1 -> chars8 m a t2 -> length t1 = length t2 -> t1 = t2.
Proof.
  intros a t1; revert a; induction t1 as [|c t1 IH]; intros a [|d t2] H1 H2 L; cbn in *; try discriminate; auto.
  destruct H1 as (E1 & _ & R1), H2 as (E2 & _ & R2). rewrite E1 in E2. apply N2Z.inj in E2. subst d.
  f_equal. apply (IH _ _ R1 R2). lia.
Qed.
Theorem string_at_functional : forall w t1 t2, string_at m w t1 -> string_at m w t2 -> t1 = t2.
Proof.
  intros w t1 t2 (F1 & L1 & S1) (F2 & L2 & S2). rewrite L1 in L2. apply fx_enc_inj in L2; [|assumption|assumption].
  apply Nat2Z.inj in L2. lay.
  destruct S1 as [(O1 & C1)|(O1 & C1)], S2 as [(O2 & C2)|(O2 & C2)].
  - apply (chars32_functional _ _ _ C1 C2 L2).
  - destruct O1 as (_ & E1), O2 as (_ & E2). rewrite E1 in E2. rewrite HWCS, HWBS in E2. discriminate.
  - destruct O1 as (_ & E1), O2 as (_ & E2). rewrite E1 in E2. rewrite HWCS, HWBS in E2. discriminate.
  - apply (chars8_functional _ _ _ C1 C2 L2).
Qed.

Lemma kv_shape : forall v w, kv v w -> wshape w.
Proof.
  intros v w H; lay; destruct H.
  - apply WFix.
  - destruct H0 as (O & _). apply (WOther _ _ O). rewrite HWB. cbn; tauto.
  - destruct H as (O & _). apply (WOther _ _ O). rewrite HWD. cbn; tauto.
  - apply (WOther _ _ H0). rewrite HWS. cbn; tauto.
  - apply WNil.
  - apply (WOther _ _ H0). rewrite HWS. cbn; tauto.
  - destruct (string_other _ _ H) as (wt & O & [-> | ->]); apply (WOther _ _ O); cbn; tauto.
  - apply WList; assumption.
  - apply (WOther _ _ H0). rewrite HWV. cbn; tauto.
  - destruct H0 as (P & _). apply WFun. rewrite <- HL11. exact P.
  - destruct H as (P & _). apply WInst. rewrite <- HL3. exact P.
  - destruct H as (P & _). apply WInst. rewrite <- HL3. exact P.
Qed.

(* The value-level meaning of each word-level test, on every represented
   value. [kl_symbolp_test] is the CL fact behind OB-REPR-SBCL-NIL: SYMBOLP
   is true on Shen [] and on Shen booleans, so Shen symbol? cannot be the raw
   CL SYMBOLP; [kl_null_test] shows CL NULL/NOT single out [] and not Shen
   false (the symbol false is CL true). *)
Lemma fx_tests : forall z,
  t_consp (fx_enc z) = false /\ t_null (fx_enc z) = false /\ t_fixnump (fx_enc z) = true /\
  t_integerp m (fx_enc z) = true /\ t_numberp m (fx_enc z) = true /\ t_stringp m (fx_enc z) = false /\
  t_arrayp m (fx_enc z) = false /\ t_symbolp m (fx_enc z) = false.
Proof.
  intro z. pose proof (fx_enc_even z) as E.
  assert (L : Z.land (fx_enc z) 15 =? 15 = false /\ (Z.land (fx_enc z) 15 =? 7) = false).
  { split; apply Z.eqb_neq; intro X; assert (Z.testbit (Z.land (fx_enc z) 15) 0 = Z.testbit (fx_enc z) 0)
      by (rewrite Z.land_spec; cbn; apply andb_true_r); rewrite X, E in H; discriminate. }
  assert (N : (fx_enc z =? nilv) = false).
  { apply Z.eqb_neq. intro X. rewrite X in E. vm_compute in E. discriminate. }
  destruct L as [L1 L2].
  unfold t_consp, t_null, t_fixnump, t_integerp, t_numberp, t_stringp, t_arrayp, t_symbolp.
  rewrite E, L1, L2, N. cbn. repeat split; reflexivity.
Qed.

Lemma nil_tests :
  t_consp nilv = false /\ t_null nilv = true /\ t_fixnump nilv = false /\ t_integerp m nilv = false /\
  t_numberp m nilv = false /\ t_stringp m nilv = false /\ t_arrayp m nilv = false /\ t_symbolp m nilv = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma ptr_tests : forall t w, ptr_ok t w -> In t [3; 11] ->
  t_consp w = false /\ t_null w = false /\ t_fixnump w = false /\ t_integerp m w = false /\
  t_numberp m w = false /\ t_stringp m w = false /\ t_arrayp m w = false /\ t_symbolp m w = false.
Proof.
  intros t w P I. pose proof (ptr_odd _ _ P ltac:(cbn in *; tauto)) as Odd.
  pose proof (ptr_not_single _ _ P ltac:(cbn in *; tauto)) as Sg.
  assert (N : (w =? nilv) = false) by (apply Z.eqb_neq; apply (ptr_ne_nil _ _ P); cbn in I; intuition; subst; discriminate).
  destruct (lowtag_eqb _ _ P) as [L1 L2].
  assert (T15 : (t =? 15) = false /\ (t =? 7) = false) by (cbn in I; intuition; subst; split; reflexivity).
  destruct T15 as [T1 T2]. rewrite T1 in L1. rewrite T2 in L2.
  unfold t_consp, t_null, t_fixnump, t_integerp, t_numberp, t_stringp, t_arrayp, t_symbolp.
  rewrite Odd, Sg, N, L1, L2. cbn. repeat split; reflexivity.
Qed.

Lemma other_tests_lemma : forall w wt, other_at m w wt ->
  t_consp w = false /\ t_null w = false /\ t_fixnump w = false /\
  t_integerp m w = (wt =? 17) /\ t_numberp m w = (wt <=? 41) /\
  t_stringp m w = ((225 <=? wt) && (wt <=? 237)) /\ t_arrayp m w = (129 <=? wt) /\
  t_symbolp m w = (wt =? 45).
Proof.
  intros w wt O. lay. destruct O as (P & Wt). rewrite HL15 in P, Wt.
  pose proof (ptr_odd _ _ P ltac:(cbn; tauto)) as Odd.
  pose proof (ptr_not_single _ _ P ltac:(cbn; tauto)) as Sg.
  assert (N : (w =? nilv) = false) by (apply Z.eqb_neq; apply (ptr_ne_nil _ _ P); vm_compute; discriminate).
  destruct (lowtag_eqb _ _ P) as [L1 L2]. cbn in L1, L2.
  assert (Hh : hdr m w = wt) by (rewrite hdr_other; [rewrite HL15; exact Wt | rewrite HL15; exact P]).
  unfold t_consp, t_null, t_fixnump, t_integerp, t_numberp, t_stringp, t_arrayp, t_symbolp.
  rewrite Odd, Sg, N, L1, L2, Hh. cbn. repeat split; reflexivity.
Qed.

Lemma cons_tests : forall w, cons_ok w ->
  t_consp w = true /\ t_null w = false /\ t_fixnump w = false /\ t_integerp m w = false /\
  t_numberp m w = false /\ t_stringp m w = false /\ t_arrayp m w = false /\ t_symbolp m w = false.
Proof.
  intros w (P & Nn). lay. rewrite HL7 in P.
  pose proof (ptr_odd _ _ P ltac:(cbn; tauto)) as Odd.
  pose proof (ptr_not_single _ _ P ltac:(cbn; tauto)) as Sg.
  assert (N : (w =? nilv) = false) by (apply Z.eqb_neq; exact Nn).
  destruct (lowtag_eqb _ _ P) as [L1 L2]. cbn in L1, L2.
  unfold t_consp, t_null, t_fixnump, t_integerp, t_numberp, t_stringp, t_arrayp, t_symbolp.
  rewrite Odd, Sg, N, L1, L2. cbn. repeat split; reflexivity.
Qed.

Theorem kl_tests : forall v w, kv v w ->
  t_consp w = kl_cons v /\ t_null w = kl_nil v /\ t_fixnump w = kl_fixnum v /\
  t_integerp m w = kl_int v /\ t_numberp m w = kl_num v /\ t_stringp m w = kl_str v /\
  t_arrayp m w = kl_array v /\ t_symbolp m w = kl_cl_symbol v.
Proof.
  intros v w H; lay; destruct H; cbn [kl_cons kl_nil kl_fixnum kl_int kl_num kl_str kl_array kl_cl_symbol].
  - destruct (fx_tests z) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    apply fx_rangeb_spec in H. rewrite A1, A2, A3, A4, A5, A6, A7, A8, H. repeat split; reflexivity.
  - destruct H0 as (O & _). rewrite HWB in O. destruct (other_tests_lemma _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. destruct (fx_rangeb z) eqn:Q; [apply fx_rangeb_spec in Q; contradiction|].
    repeat split; reflexivity.
  - destruct H as (O & _). rewrite HWD in O. destruct (other_tests_lemma _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - unfold symbol_at in H0. rewrite HWS in H0. destruct (other_tests_lemma _ _ H0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - destruct nil_tests as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - unfold symbol_at in H0. rewrite HWS in H0. destruct (other_tests_lemma _ _ H0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - destruct (string_other _ _ H) as (wt & O & [-> | ->]);
      destruct (other_tests_lemma _ _ O) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8);
      rewrite A1, A2, A3, A4, A5, A6, A7, A8; repeat split; reflexivity.
  - destruct (cons_tests _ H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - unfold vector_hdr in H0. rewrite HWV in H0. destruct (other_tests_lemma _ _ H0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - destruct H0 as (P & _). rewrite HL11 in P. destruct (ptr_tests 11 _ P ltac:(cbn; tauto)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. destruct v; cbn in H; try contradiction; repeat split; reflexivity.
  - destruct H as (P & _). rewrite HL3 in P. destruct (ptr_tests 3 _ P ltac:(cbn; tauto)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
  - destruct H as (P & _). rewrite HL3 in P. destruct (ptr_tests 3 _ P ltac:(cbn; tauto)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    rewrite A1, A2, A3, A4, A5, A6, A7, A8. repeat split; reflexivity.
Qed.

(* ---------------------------------------------------------------- what this relation is and is not *)

(* Shen-CL booleans are CL symbols: the word of VBool true also represents
   the Shen symbol true. *)
Theorem kl_bool_symbol_collision : forall b w, kv (VBool b) w -> kv (VSym (bool_text b)) w.
Proof. intros b w H. inversion H; subst; [apply KSym; assumption | cbn in *; contradiction]. Qed.

Theorem kl_false_is_cl_true : forall w, kv (VBool false) w -> t_null w = false /\ w <> nilv.
Proof.
  intros w H. destruct (kl_tests _ _ H) as (_ & N & _). split; [exact N|].
  intro E. subst w. unfold t_null in N. rewrite Z.eqb_refl in N. discriminate.
Qed.

(* Immediates and pointers are disjoint: fixnum words are even, every other
   represented word is odd (an odd lowtag), and NIL is not a cons. *)
Theorem immediate_pointer_disjoint : forall v w, kv v w ->
  (Z.testbit w 0 = false <-> exists z, v = VNum (NInt z) /\ fx_range z /\ w = fx_enc z).
Proof.
  intros v w H. destruct (kl_tests _ _ H) as (_ & _ & F & _). unfold t_fixnump in F.
  split.
  - intro E. rewrite E in F. cbn in F. destruct v as [[z|b]| | | | | | | | | | |]; cbn in F; try discriminate.
    symmetry in F. apply fx_rangeb_spec in F. exists z. split; [reflexivity|]. split; [exact F|].
    inversion H; subst; [reflexivity|contradiction|cbn in *; contradiction].
  - intros (z & -> & R & ->). apply fx_enc_even.
Qed.

(* ---------------------------------------------------------------- memory operations *)

Theorem car_cdr_repr : forall a d w, kv (VCons a d) w ->
  cons_ok w /\ kv a (car_w m w) /\ kv d (cdr_w m w) /\
  (w - img_list_pointer_lowtag + 8 * img_cons_car_slot) mod 8 = 0 /\
  (w - img_list_pointer_lowtag + 8 * img_cons_cdr_slot) mod 8 = 0.
Proof.
  intros a d w H; inversion H; subst; [|cbn in *; contradiction].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  destruct H2 as ((_ & L & _) & _). split; apply slot_aligned; exact L.
Qed.

Theorem vector_ref_repr : forall h l w cells i v, heap_rel h -> kv (VVec l) w ->
  nth_error h l = Some cells -> nth_error cells i = Some v ->
  kv v (slot m img_other_pointer_lowtag w (img_vector_data_offset + Z.of_nat i)) /\
  slot m img_other_pointer_lowtag w img_vector_length_slot = fx_enc (Z.of_nat (length cells)).
Proof.
  intros h l w cells i v (LI & HR) R E1 E2.
  inversion R; subst; [|cbn in *; contradiction].
  destruct (HR _ _ E1) as (w' & L' & (_ & Len & Cells)).
  match goal with Hl : loc l = Some w |- _ => rewrite Hl in L' end.
  inversion L'; subst. split; [apply Cells; assumption | exact Len].
Qed.

End Rel.

(* The captured SBCL code on Shen values: for every represented value, the
   inline CONSP/NULL/NOT/SYMBOLP/STRINGP/NUMBERP/INTEGERP/TYPEP FIXNUM/ARRAYP
   code returns T exactly on the values the kl_* predicates name. In
   particular SYMBOLP answers T on Shen [] and on both Shen booleans, and
   NULL/NOT answer NIL on Shen false. *)
Theorem kl_machine_tests : forall m loc symw proc port cond v w s,
  kv m loc symw proc port cond v w -> regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_consp s (kl_cons v) /\ yields m w_null s (kl_nil v) /\ yields m w_not s (kl_nil v) /\
  yields m w_symbolp s (kl_cl_symbol v) /\ yields m w_stringp s (kl_str v) /\
  yields m w_numberp s (kl_num v) /\ yields m w_integerp s (kl_int v) /\
  yields m w_typep_fixnum s (kl_fixnum v) /\ yields m w_arrayp s (kl_array v).
Proof.
  intros m loc symw proc port cond v w s H Ok H11 H26.
  destruct (kl_tests _ _ _ _ _ _ _ _ H) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  rewrite <- A1, <- A2, <- A3, <- A4, <- A5, <- A6, <- A7, <- A8.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply consp_window; assumption.
  - apply null_window; assumption.
  - apply not_window; assumption.
  - apply symbolp_window; assumption.
  - apply stringp_window; assumption.
  - apply numberp_window; assumption.
  - apply integerp_window; assumption.
  - apply typep_fixnum_window; assumption.
  - apply arrayp_window; assumption.
Qed.

End SbclValues.
