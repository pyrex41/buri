(* E2E-20 first byte-level lemma against the authoritative Armv9.4-A model.

   NOT a scripts/prove module.  It needs the separate toolchain recorded in
   docs/ARM-FOUNDATION.md section 10 (nixpkgs Coq 8.18.0, stdpp 1.10.0,
   coq-sail-stdpp 0.19, the sail-arm 7d058164 arm-v9.4-a Coq snapshot compiled
   with -R . SailArm).  Checked only by the opt-in scripts/check-arm.sh, which
   first binds `chez_word_0014` to bytes 0x14..0x17 of
   ports/arm/chez/chez1030-buri-arm-add.bin.

   Subject: the Chez Scheme 10.3.0 tarm64le word at kl:buri-arm-add+0x14,
   bytes 17 00 01 ab (little-endian word 0xab010017, ADDS X23, X0, X1).

   What is proved, and of which evidence kind:
   * chez_0014_decode (universal over pc): the model's own monadic decoder
     __DecodeA64 on this exact word IS the program
       read SEE; if SEE < 15 then (write SEE := 15; execute ADDS(d=23,n=0,m=1,
       64-bit, setflags, LSL #0)) else throw Error_Undefined.
     This is an equation between iMon trees, so it fixes every behaviour,
     including the SEE-dependent one.  The SEE premise is therefore explicit
     in the statement rather than assumed.
   * chez_0014_execute (closed equation): that execute call equals the
     explicit register-transfer program adds_x23_x0_x1.
   * chez_0014_adds_trace (universal over pc, SEE value, X0, X1, PSTATE):
     under SEE < 15 the decoder admits, in coq-sail's own trace semantics
     Interface.iTrace_match, the trace that reads X0/X1/PSTATE with those
     values (each PSTATE re-read returning the last written value, i.e. a
     sequential register state) and writes PSTATE.{N,Z,C,V} from the model's
     AddWithCarry and X23 := the 64-bit sum.  iTrace_match is a "this trace is
     a behaviour" relation; uniqueness of behaviour is given by the equations
     above, not by this corollary.
   * chez_0014_sum: uint of the value written to X23 is (uint X0 + uint X1)
     mod 2^64.
   Trusted: the Sail-to-Coq translation (the Coq text is the model), coq-sail
   0.19's monad and trace definitions, Coq 8.18.0 + stdpp 1.10.0, and the
   three Coq standard-library Reals axioms that `Print Assumptions` reports
   for any statement mentioning __DecodeA64 (the model's floating-point
   decoders use Coq Reals through coq-sail's Real.v).  No axiom is added
   here; chez_0014_execute and the bitvector lemmas are closed. *)
Require Import SailStdpp.Base.
Require Import armv9_types armv9.
From stdpp.bitvector Require Import definitions tactics.
Import Defs.
Open Scope Z.

(* The exact captured word; scripts/check-arm.sh regenerates this line from
   the stored bytes and compares. *)
Definition chez_word_0014 : mword 32 := Ox"AB010017".

(* Decide one closed Boolean guard by computation; leave open guards alone. *)
Ltac decide_guard :=
  match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch b with true => fail | false => fail | _ =>
        let v := eval vm_compute in b in
        lazymatch v with true => idtac | false => idtac end;
        let H := fresh in
        assert (H : b = v) by (vm_compute; reflexivity);
        rewrite H; clear H; cbv beta iota
      end
  end.

Ltac mstep :=
  repeat (first [decide_guard
                | progress cbn [and_boolM or_boolM bind bind0 returnM returnm
                                Interface.iMon_bind read_reg Defs.read_reg
                                assert_exp' Defs.assert_exp' neq_int]]).

Theorem chez_0014_decode pc :
  __DecodeA64 pc chez_word_0014 =
  (read_reg SEE >>= fun see : Z =>
     if Z.ltb see 15 then
       write_reg SEE 15 >>
       execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
         23 64 1 0 true 0 ShiftType_LSL false
     else throw (Error_Undefined tt)).
Proof.
  unfold __DecodeA64.
  repeat decide_guard.
  unfold __DecodeA64_DataProcReg.
  mstep.
  unfold decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg,
    DecodeShift.
  cbv zeta.
  mstep.
  reflexivity.
Qed.

(* The register-transfer program, written with the model's own primitives. *)
Definition adds_x23_x0_x1 : M unit :=
  undefined_bitvector 64 >>= fun _ =>
  read_reg R0 >>= fun a : mword 64 =>
  read_reg R1 >>= fun b : mword 64 =>
  undefined_bitvector 4 >>= fun _ =>
  undefined_bitvector 1 >>= fun _ =>
  let r := AddWithCarry (autocast (subrange_vec_dec a (64 - 1) 0) : mword 64)
                        (shiftl (autocast (subrange_vec_dec b (64 - 1) 0) : mword 64) 0)
                        ('b"0" : mword 1) in
  read_reg PSTATE >>= fun p0 =>
  write_reg PSTATE {[ p0 with ProcState_N := subrange_vec_dec (snd r) 3 3 ]} >>
  read_reg PSTATE >>= fun p1 =>
  write_reg PSTATE {[ p1 with ProcState_Z := subrange_vec_dec (snd r) 2 2 ]} >>
  read_reg PSTATE >>= fun p2 =>
  write_reg PSTATE {[ p2 with ProcState_C := subrange_vec_dec (snd r) 1 1 ]} >>
  read_reg PSTATE >>= fun p3 =>
  write_reg PSTATE {[ p3 with ProcState_V := subrange_vec_dec (snd r) 0 0 ]} >>
  write_reg R23 (zero_extend (fst r) 64).

Theorem chez_0014_execute :
  execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
    23 64 1 0 true 0 ShiftType_LSL false = adds_x23_x0_x1.
Proof.
  unfold execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg, X_read,
    ShiftReg, X_set, __id, read_gpr, write_gpr, adds_x23_x0_x1.
  mstep.
  reflexivity.
Qed.

(* Bitvector facts about the model's casts, all closed. *)
Lemma subrange_full_64 (x : mword 64) :
  (autocast (subrange_vec_dec x (64 - 1) 0) : mword 64) = x.
Proof.
  unfold subrange_vec_dec, to_word_idx.
  rewrite !(autocast_eq _ eq_refl). cbn.
  rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold MachineWord.MachineWord.slice, get_word.
  rewrite !cast_Z_refl. unfold to_word.
  change (Z.to_N (64 - 1 - 0 + 1)) with 64%N.
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_wrap_small. apply (bv_unsigned_in_range 64 x).
Qed.

Lemma shiftl_0_64 (x : mword 64) : shiftl x 0 = x.
Proof.
  unfold shiftl, with_word. cbn.
  unfold MachineWord.MachineWord.logical_shift_left, MachineWord.MachineWord.N_to_word.
  cbn. apply bv_eq. rewrite bv_shiftl_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.shiftl_0_r.
  apply bv_wrap_small. apply (bv_unsigned_in_range 64 x).
Qed.

Lemma zero_extend_64 (x : mword 64) : zero_extend x 64 = x.
Proof.
  unfold zero_extend, extz_vec, to_word. cbn.
  unfold MachineWord.MachineWord.zero_extend, get_word.
  apply bv_eq. rewrite bv_zero_extend_unsigned; [reflexivity | lia].
Qed.

Definition adds_nzcv (x0 x1 : mword 64) : mword 4 :=
  snd (AddWithCarry x0 x1 ('b"0" : mword 1)).
Definition adds_sum (x0 x1 : mword 64) : mword 64 :=
  fst (AddWithCarry x0 x1 ('b"0" : mword 1)).
Definition ps_N x0 x1 (p : ProcState) :=
  {[ p with ProcState_N := subrange_vec_dec (adds_nzcv x0 x1) 3 3 ]}.
Definition ps_NZ x0 x1 p :=
  {[ ps_N x0 x1 p with ProcState_Z := subrange_vec_dec (adds_nzcv x0 x1) 2 2 ]}.
Definition ps_NZC x0 x1 p :=
  {[ ps_NZ x0 x1 p with ProcState_C := subrange_vec_dec (adds_nzcv x0 x1) 1 1 ]}.
Definition ps_NZCV x0 x1 p :=
  {[ ps_NZC x0 x1 p with ProcState_V := subrange_vec_dec (adds_nzcv x0 x1) 0 0 ]}.

Definition Ev := Interface.iEvent (fun _ : Type => exception).

Definition adds_events (see : Z) (x0 x1 : mword 64) (p : ProcState) : list Ev :=
  [ Interface.IEvent (Interface.RegRead SEE None) see;
    Interface.IEvent (Interface.RegWrite SEE None 15) tt;
    Interface.IEvent (Interface.RegRead R0 None) x0;
    Interface.IEvent (Interface.RegRead R1 None) x1;
    Interface.IEvent (Interface.RegRead PSTATE None) p;
    Interface.IEvent (Interface.RegWrite PSTATE None (ps_N x0 x1 p)) tt;
    Interface.IEvent (Interface.RegRead PSTATE None) (ps_N x0 x1 p);
    Interface.IEvent (Interface.RegWrite PSTATE None (ps_NZ x0 x1 p)) tt;
    Interface.IEvent (Interface.RegRead PSTATE None) (ps_NZ x0 x1 p);
    Interface.IEvent (Interface.RegWrite PSTATE None (ps_NZC x0 x1 p)) tt;
    Interface.IEvent (Interface.RegRead PSTATE None) (ps_NZC x0 x1 p);
    Interface.IEvent (Interface.RegWrite PSTATE None (ps_NZCV x0 x1 p)) tt;
    Interface.IEvent (Interface.RegWrite R23 None (adds_sum x0 x1)) tt ].

Ltac tstep :=
  cbv beta iota zeta delta [bind bind0 returnM returnm Interface.iMon_bind read_reg write_reg
       Defs.read_reg Defs.write_reg undefined_bitvector
       choose_bitvector mret Interface.iMon_mret_inst];
  first [ apply Interface.TMSuccess
        | apply Interface.TMNext
        | eapply Interface.TMChoose; [cbv [choose_type]; exact inhabitant |] ].

Theorem chez_0014_adds_trace pc (see : Z) (x0 x1 : mword 64) (p : ProcState) :
  see < 15 ->
  Interface.iTrace_match (__DecodeA64 pc chez_word_0014)
    (adds_events see x0 x1 p, inl tt).
Proof.
  intros Hsee.
  rewrite chez_0014_decode.
  unfold adds_events.
  tstep.
  cbn [bind Interface.iMon_bind returnM returnm].
  replace (Z.ltb see 15) with true by (symmetry; apply Z.ltb_lt; exact Hsee).
  tstep.
  rewrite chez_0014_execute. unfold adds_x23_x0_x1.
  repeat tstep.
  rewrite !subrange_full_64, shiftl_0_64.
  repeat tstep.
  rewrite zero_extend_64.
  repeat tstep.
Qed.

Lemma chez_0014_sum (x0 x1 : mword 64) :
  uint (adds_sum x0 x1) = (uint x0 + uint x1) mod 2 ^ 64.
Proof.
  unfold adds_sum, AddWithCarry. cbn [fst].
  change (uint ('b"0" : mword 1)) with 0. rewrite Z.add_0_r.
  generalize (uint x0 + uint x1) as s. intros s.
  unfold integer_subrange. rewrite get_slice_int_eta. unfold get_slice_int'.
  destruct (sumbool_of_bool _) as [h|h]; [|vm_compute in h; discriminate h].
  rewrite !(autocast_eq _ eq_refl), !cast_Z_refl.
  unfold subrange_vec_dec, to_word_idx.
  rewrite (autocast_eq _ eq_refl), cast_Z_refl, MachineWord.MachineWord.cast_idx_refl.
  unfold uint, MachineWord.MachineWord.word_to_N, MachineWord.MachineWord.slice, get_word,
    to_word, mword_of_int, MachineWord.MachineWord.Z_to_word.
  repeat match goal with |- context [Z.to_N ?e] =>
    lazymatch e with bv_unsigned _ => fail | _ =>
    let v := eval vm_compute in (Z.to_N e) in change (Z.to_N e) with v end end.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Zmod_mod. reflexivity.
Qed.

Print Assumptions chez_0014_decode.
Print Assumptions chez_0014_execute.
Print Assumptions chez_0014_adds_trace.
Print Assumptions chez_0014_sum.
Print Assumptions __DecodeA64.
