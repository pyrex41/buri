(* E2E-21 (CL side): what the captured SBCL 2.6.8 arm64 code for the
   E2E-21 host operations decides, as a function of the argument words.

   For each operation (EQ, TYPEP FIXNUM, INTEGERP, NUMBERP, CONSP, STRINGP,
   ARRAYP, SYMBOLP, NOT, NULL) the pinned aarch64 image compiled
   (lambda (x) (op x)) to an inline type test (sbcl-type-tests.lisp; the
   words are in SbclTypeTests, generated). [frame_*] are ground derivations:
   the decoded function is the standard external entry point (argument
   count check, argument moved from R0 to the register the test reads), the
   test window, and the standard single-value return; the window leaves its
   Boolean in R0 (x10). [*_window] are universal theorems: for every
   register file in which the argument register holds any word w and the
   NULL register holds NIL, and every memory, running the decoded window
   reaches the window's end with R0 = T or NIL, exactly as the word-level
   test [t_*] says. STRING=, EQUAL, EQL and = are not inline: [full_calls]
   shows each compiles to a tail branch through a function object (BR LR),
   so their contracts stay with E2E-24.

   The argument is untyped in the captured functions. SBCL emits shorter
   code when it has derived a type for the argument (type-vops.lisp); those
   variants are not covered here.

   [*_source] lemmas are ground derivations linking the captured code to
   the pinned sources: for every header widetag value of the early-objdef
   enumeration (17 + 4k, k < 60) the captured header test agrees with
   membership in the define-type-vop type-code list. *)
From Coq Require Import ZArith List Bool Lia.
From Buri Require Import SbclLayout SbclA64 SbclTypeTests.
Import ListNotations.
Open Scope Z_scope.
Module SbclTests.
Import SbclLayout.SbclLayout SbclA64.SbclA64 SbclTypeTests.SbclTypeTests.

Definition window (ws : list Z) (i j : nat) : list Z := firstn (j - i) (skipn i ws).
Definition nilv : Z := img_nil_value.
Definition tv : Z := nilv + 56.
(* The byte LDURB [x, #-15] reads: the widetag of an other-pointer object. *)
Definition hdr (m : Z -> Z) (w : Z) : Z := m (trunc 64 (w + -15)) mod 256.

Definition w_eq := window code_eq 7 10.
Definition w_typep_fixnum := window code_typep_fixnum 7 10.
Definition w_integerp := window code_integerp 7 17.
Definition w_numberp := window code_numberp 7 19.
Definition w_consp := window code_consp 7 12.
Definition w_stringp := window code_stringp 7 17.
Definition w_arrayp := window code_arrayp 7 16.
Definition w_symbolp := window code_symbolp 7 18.
Definition w_not := window code_not 7 10.
Definition w_null := window code_null 7 10.

(* ---------------------------------------------------------------- word-level tests *)
Definition t_eq (x y : Z) : bool := x =? y.
Definition t_fixnump (w : Z) : bool := negb (Z.testbit w 0).
Definition t_integerp (m : Z -> Z) (w : Z) : bool :=
  negb (Z.testbit w 0) || ((Z.land w 15 =? 15) && (hdr m w =? 17)).
Definition t_numberp (m : Z -> Z) (w : Z) : bool :=
  negb (Z.testbit w 0) || (trunc 32 w =? 25) || ((Z.land w 15 =? 15) && (hdr m w <=? 41)).
Definition t_consp (w : Z) : bool := (Z.land w 15 =? 7) && negb (w =? nilv).
Definition t_stringp (m : Z -> Z) (w : Z) : bool :=
  (Z.land w 15 =? 15) && ((225 <=? hdr m w) && (hdr m w <=? 237)).
Definition t_arrayp (m : Z -> Z) (w : Z) : bool := (Z.land w 15 =? 15) && (129 <=? hdr m w).
Definition t_symbolp (m : Z -> Z) (w : Z) : bool := (w =? nilv) || ((Z.land w 15 =? 15) && (hdr m w =? 45)).
Definition t_null (w : Z) : bool := w =? nilv.

(* The window ends with R0 holding T if b, NIL otherwise. Every branch in
   the windows is forward, so length + 1 steps of fuel always suffice. *)
Definition yields (m : Z -> Z) (ws : list Z) (s : state) (b : bool) : Prop :=
  exists s', run_words (S (length ws)) m ws s = Some s' /\ R s' 10 = if b then tv else nilv.

(* ---------------------------------------------------------------- ground facts *)

Lemma sbcl_capture_consts :
  cap_nil_value = img_nil_value /\ cap_t_address = tv /\ nilv mod 16 = img_list_pointer_lowtag /\
  tv mod 16 = img_other_pointer_lowtag /\ src_reg_null = 26 /\ src_reg_r0 = 10 /\ src_reg_r1 = 11 /\
  src_reg_r2 = 12 /\ src_reg_lr = 30 /\ src_reg_cfp = 29 /\ src_reg_csp = 27 /\ src_reg_thread = 21 /\
  src_reg_nargs = 23 /\ src_arg_reg0_is_r0 = 1 /\ src_arg_reg1_is_r1 = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The standard external entry point of an n-argument function whose test
   reads register r: STR LR; CMP NARGS, #(fixnum n); B.NE to the trap;
   ADD CSP; MOV r, R0; LDR R0, [THREAD, #16]; STR R0, [CFP, #16]. *)
Definition xep (n r off : Z) : list (option instr) :=
  [Some (IStrX 30 29 8); Some (IAddSubImm true true true 31 23 (2 * n)); Some (IBcond CNE off);
   Some (IAddSubImm true false false 27 29 24); Some (ILogReg true 1 r 31 10);
   Some (ILdrX 10 21 16); Some (IStrX 10 29 16)].
(* Single-value return, then the argument-count trap (BRK, not decoded). *)
Definition epi : list (option instr) :=
  [Some (ILogReg true 1 27 31 29); Some (IAddSubImm true true true 31 26 0);
   Some (ILdpX 29 30 29 0); Some (IRet 30); None].

Lemma frame_ground :
  firstn 7 (map decode code_eq) = xep 2 12 12 /\ skipn 10 (map decode code_eq) = epi /\
  firstn 7 (map decode code_typep_fixnum) = xep 1 11 12 /\ skipn 10 (map decode code_typep_fixnum) = epi /\
  firstn 7 (map decode code_integerp) = xep 1 11 19 /\ skipn 17 (map decode code_integerp) = epi /\
  firstn 7 (map decode code_numberp) = xep 1 11 21 /\ skipn 19 (map decode code_numberp) = epi /\
  firstn 7 (map decode code_consp) = xep 1 11 14 /\ skipn 12 (map decode code_consp) = epi /\
  firstn 7 (map decode code_stringp) = xep 1 11 19 /\ skipn 17 (map decode code_stringp) = epi /\
  firstn 7 (map decode code_arrayp) = xep 1 11 18 /\ skipn 16 (map decode code_arrayp) = epi /\
  firstn 7 (map decode code_symbolp) = xep 1 11 20 /\ skipn 18 (map decode code_symbolp) = epi /\
  firstn 7 (map decode code_not) = xep 1 11 12 /\ skipn 10 (map decode code_not) = epi /\
  firstn 7 (map decode code_null) = xep 1 11 12 /\ skipn 10 (map decode code_null) = epi.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* In eq, x is moved to R2 (x12) and y stays in R1 (x11): the prologue's only
   other register write is R0. *)

(* STRING=, EQUAL, EQL and = end in an indirect tail branch through a
   function object, and contain no RET: they are full calls. *)
Definition is_br30 (w : Z) : bool := (fld w 10 22 =? 3508160) && (fld w 0 5 =? 0) && (fld w 5 5 =? 30).
Definition tail_calls (ws : list Z) : bool :=
  existsb is_br30 ws && negb (existsb (fun w => match decode w with Some (IRet _) => true | _ => false end) ws).
Lemma full_calls :
  tail_calls code_string_eq = true /\ tail_calls code_equal = true /\ tail_calls code_eql = true /\
  tail_calls code_num_eq = true /\
  tail_calls code_consp = false /\ tail_calls code_eq = false /\ tail_calls code_symbolp = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The quoted generator and genesis lines are present in the pinned sources. *)
Lemma sbcl_source_flags :
  srcflag_consp_vop = 1 /\ srcflag_symbolp_vop_nil_first = 1 /\ srcflag_fixnump_vop = 1 /\
  srcflag_test_fixnum_tbz = 1 /\ srcflag_if_eq_translate_eq = 1 /\ srcflag_if_eq_cmp = 1 /\
  srcflag_nil_symbol_header_widetag = 1 /\ srcflag_nil_car_is_nil = 1 /\ srcflag_nil_cdr_is_nil = 1 /\
  srcflag_nil_val_offset = 1 /\ srcflag_fixnum_lowtags_even = 1 /\ srcflag_other_pointer_vops_symbolp = 1 /\
  tv_integerp_fixnum = 1 /\ tv_numberp_fixnum = 1 /\ tv_fixnump_fixnum = 1 /\ tv_fixnump_codes = [] /\
  tv_stringp_fixnum = 0 /\ tv_non_null_symbol_p_fixnum = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Header widetag values of the early-objdef enumeration (start 17, step 4). *)
Definition header_widetags : list Z := map (fun k => 17 + 4 * Z.of_nat k) (seq 0 60).
Definition agrees (test : Z -> bool) (codes : list Z) : bool :=
  forallb (fun h => Bool.eqb (test h) (existsb (Z.eqb h) codes)) header_widetags.
Lemma header_widetags_source :
  hd 0 header_widetags = src_bignum_widetag /\ last header_widetags 0 = src_unused_array_widetag /\
  src_ratio_widetag = src_bignum_widetag + 4 /\ src_symbol_widetag = 45 /\ src_simple_array_widetag = 129 /\
  src_complex_array_widetag = 249.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tests_match_sources :
  agrees (fun h => h =? 17) tv_integerp_codes = true /\
  agrees (fun h => h <=? 41) tv_numberp_codes = true /\
  agrees (fun h => (225 <=? h) && (h <=? 237)) tv_stringp_codes = true /\
  agrees (fun h => h =? 45) tv_non_null_symbol_p_codes = true /\
  In src_single_float_widetag tv_numberp_codes /\ src_single_float_widetag = 25.
Proof. vm_compute. repeat split; try reflexivity; tauto. Qed.

(* ---------------------------------------------------------------- symbolic execution *)

Lemma land15 : forall w, 0 <= Z.land w 15 < 16.
Proof. intro w. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma land1 : forall w, 0 <= Z.land w 1 < 2.
Proof. intro w. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma byte_rng : forall x, 0 <= x mod 256 < 256.
Proof. intro x. apply Z.mod_pos_bound. lia. Qed.
Lemma trunc_land15 : forall w, trunc 64 (Z.land w 15) = Z.land w 15.
Proof. intro w. apply trunc_small; pose proof (land15 w); lia. Qed.
Lemma trunc_land1 : forall w, trunc 64 (Z.land w 1) = Z.land w 1.
Proof. intro w. apply trunc_small; pose proof (land1 w); lia. Qed.
Lemma trunc_byte : forall x, trunc 64 (x mod 256) = x mod 256.
Proof. intro x. apply trunc_small; pose proof (byte_rng x); lia. Qed.
Lemma nilv_rng : 0 <= nilv < 2 ^ 63.
Proof. unfold nilv, img_nil_value. lia. Qed.
Lemma land1_testbit : forall w, (Z.land w 1 =? 0) = negb (Z.testbit w 0).
Proof.
  intro w. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
  destruct (Z.testbit w 0) eqn:E; [rewrite Z.testbit_true in E by lia|rewrite Z.testbit_false in E by lia];
  rewrite Z.div_1_r in E; change (2 ^ 1) with 2; rewrite E; reflexivity.
Qed.

(* Symbolic execution: keep a symbolic pc folded until its branch condition
   is split, so every proof step stays small. *)
Local Arguments nth_z {A} !l !k.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Ltac closed c := match c with context [?v] => is_var v; fail 1 | _ => idtac end.

Ltac small := match goal with
  | |- trunc 64 (?y mod 256) < _ => rewrite trunc_byte; pose proof (byte_rng y); lia
  | |- trunc 64 ?c < _ => closed c; vm_compute; reflexivity end.

Ltac norm W :=
  repeat rewrite addsub_eta;
  repeat (rewrite as_r_add || (rewrite as_r_sub_t by lia) || (rewrite as_z_t by lia)
          || (rewrite as_c_t by lia) || (rewrite as_nv_t by (lia || small)));
  repeat (rewrite trunc_land15 || rewrite trunc_land1 || rewrite trunc_byte || rewrite trunc_trunc);
  repeat match goal with
   | H : 0 <= ?v < 2 ^ 64 |- context [trunc 64 ?v] => rewrite (trunc_small 64 v) by lia
   | |- context [trunc 64 nilv] => rewrite (trunc_small 64 nilv) by (pose proof nilv_rng; lia)
   | |- context [trunc 64 (nilv + 56)] => change (trunc 64 (nilv + 56)) with tv
   | |- context [trunc ?n ?c] => lazymatch c with context [nilv] => fail | _ => closed c;
       let v := eval vm_compute in (trunc n c) in change (trunc n c) with v end
   end.

Ltac exec1 rw W :=
  repeat (progress (cbn -[addsub as_r as_n as_z as_c as_v Z.land trunc nilv tv Z.testbit Z.modulo];
                    rw; norm W)).
Ltac atom W := match goal with |- context [if ?b then _ else _] =>
  match b with
  | context [Z.testbit W ?k] => let E := fresh "C" in destruct (Z.testbit W k) eqn:E
  | context [?x =? ?y] => lazymatch constr:((x, y)) with context [if _ then _ else _] => fail | context [W] =>
      let E := fresh "C" in destruct (x =? y) eqn:E end
  | context [?x <=? ?y] => lazymatch constr:((x, y)) with context [if _ then _ else _] => fail | context [W] =>
      let E := fresh "C" in destruct (x <=? y) eqn:E end
  end end.
Ltac exec rw W := repeat (progress (exec1 rw W; try atom W)); try reflexivity.
Ltac dec := unfold run_words; match goal with |- context [decode_all ?ws] =>
  let x := eval vm_compute in (decode_all ws) in change (decode_all ws) with x end.

Lemma yields_of : forall m ws s (b : bool),
  match run_words (S (length ws)) m ws s with Some s' => R s' 10 = (if b then tv else nilv) | None => False end ->
  yields m ws s b.
Proof. intros m ws s b H. unfold yields. destruct (run_words (S (length ws)) m ws s); [eauto|contradiction]. Qed.

(* Machine forms of two tests, and their meaning on header bytes. *)
Lemma ble_41 : forall b, negb (negb (b =? 41) && (41 <=? b)) = (b <=? 41).
Proof. intro b. destruct (Z.eqb_spec b 41), (Z.leb_spec 41 b), (Z.leb_spec b 41); cbn; try reflexivity; lia. Qed.
Lemma bls_string : forall b, 0 <= b < 256 ->
  negb ((12 <=? trunc 64 (b - 225)) && negb (trunc 64 (b - 225) =? 12)) = (225 <=? b) && (b <=? 237).
Proof.
  intros b Hb. unfold trunc. change (2 ^ 64) with 18446744073709551616. destruct (Z.leb_spec 225 b).
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec 12 (b - 225)), (Z.eqb_spec (b - 225) 12), (Z.leb_spec b 237); cbn; try reflexivity; lia.
  - rewrite <- (Z.mod_unique (b - 225) 18446744073709551616 (-1) (b - 225 + 18446744073709551616)) by lia.
    destruct (Z.leb_spec 12 (b - 225 + 18446744073709551616)), (Z.eqb_spec (b - 225 + 18446744073709551616) 12);
      cbn; try reflexivity; lia.
Qed.

(* ---------------------------------------------------------------- the windows *)

Theorem eq_window : forall m s x y, regs_ok s -> R s 12 = x -> R s 11 = y -> R s 26 = nilv ->
  yields m w_eq s (t_eq x y).
Proof.
  intros m s x y Ok H12 H11 H26; apply yields_of; unfold t_eq; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11. pose proof (Ok 12) as O12; rewrite H12 in O12.
  exec ltac:(rewrite ?H11, ?H12, ?H26) y.
Qed.

Theorem typep_fixnum_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_typep_fixnum s (t_fixnump w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_fixnump; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  rewrite <- land1_testbit. exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem integerp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_integerp s (t_integerp m w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_integerp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  unfold hdr.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem numberp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_numberp s (t_numberp m w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_numberp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  unfold hdr. rewrite <- ble_41.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem consp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_consp s (t_consp w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_consp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem stringp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_stringp s (t_stringp m w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_stringp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  rewrite <- (bls_string (hdr m w)) by apply byte_rng. unfold hdr.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem arrayp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_arrayp s (t_arrayp m w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_arrayp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  unfold hdr.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem symbolp_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_symbolp s (t_symbolp m w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_symbolp; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  unfold hdr.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem not_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_not s (t_null w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_null; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

Theorem null_window : forall m s w, regs_ok s -> R s 11 = w -> R s 26 = nilv ->
  yields m w_null s (t_null w).
Proof.
  intros m s w Ok H11 H26; apply yields_of; unfold t_null; dec.
  pose proof (Ok 11) as O11; rewrite H11 in O11.
  exec ltac:(rewrite ?H11, ?H26) w.
Qed.

(* NOT and NULL compile to the same instructions. *)
Lemma not_null_same_code : code_not = code_null.
Proof. vm_compute. reflexivity. Qed.

End SbclTests.
