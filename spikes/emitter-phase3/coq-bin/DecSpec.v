(** * [decode] of overlay/check_fn.c, transcribed into Rocq, and the byte layout of its result.

    [cdec] follows the C line by line: [dec16] and [dec32] with their [bit] and [sx] helpers, and
    [decode] choosing between them on the low two bits.  Fields are integers; [imm] is the C's
    [i64].  The C's shifts of negative values ([imm << 12]) are read as the compiler emits them,
    multiplication by 4096.  [encb] is [Ins] as clang lays it out (DWARF: k@0 rd@4 r1@8 r2@12
    imm@16 len@24, size 32), padding included, since the compiled code writes the padding too. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
Import ListNotations.
Open Scope Z_scope.

(** enum ik *)
Definition I_BAD := 0. Definition I_ADDI := 1. Definition I_ANDI := 2. Definition I_ADD := 3.
Definition I_XOR := 4. Definition I_SLLI := 5. Definition I_LUI := 6. Definition I_AUIPC := 7.
Definition I_LD := 8. Definition I_SD := 9. Definition I_BEQ := 10. Definition I_BNE := 11.
Definition I_BLTU := 12. Definition I_BGEU := 13. Definition I_JAL := 14. Definition I_JALR := 15.

Record ins := mkI { ik : Z; ird : Z; ir1 : Z; ir2 : Z; iimm : Z; ilen : Z }.

(** [bit(w, hi, lo)] and [sx(v, bits)] *)
Definition bitz (w hi lo : Z) : Z := Z.land (Z.shiftr w lo) (Z.ones (hi - lo + 1)).
Definition sx (v : Z) (bits : N) : Z := bv_swrap bits v.

Definition dec16 (w : Z) : ins :=
  let bad := mkI I_BAD 0 0 0 0 2 in
  let op := Z.land w 3 in let f3 := bitz w 15 13 in let rd := bitz w 11 7 in let rs2 := bitz w 6 2 in
  let rdp := bitz w 4 2 + 8 in let rs1p := bitz w 9 7 + 8 in
  if op =? 0 then
    let d := Z.lor (Z.shiftl (bitz w 12 10) 3) (Z.shiftl (bitz w 6 5) 6) in
    if (f3 =? 0) && negb (w =? 0) then
      let n := Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w 12 11) 4) (Z.shiftl (bitz w 10 7) 6))
                            (Z.shiftl (bitz w 6 6) 2)) (Z.shiftl (bitz w 5 5) 3) in
      if negb (n =? 0) then mkI I_ADDI rdp 2 0 n 2 else bad
    else if f3 =? 3 then mkI I_LD rdp rs1p 0 d 2
    else if f3 =? 7 then mkI I_SD 0 rs1p rdp d 2
    else bad
  else if op =? 1 then
    let imm := sx (Z.lor (Z.shiftl (bitz w 12 12) 5) (bitz w 6 2)) 6 in
    if f3 =? 0 then mkI I_ADDI rd rd 0 imm 2
    else if f3 =? 2 then mkI I_ADDI rd 0 0 imm 2
    else if (f3 =? 3) && negb (rd =? 2) && negb (rd =? 0) && negb (imm =? 0) then mkI I_LUI rd 0 0 (imm * 4096) 2
    else if (f3 =? 4) && (bitz w 11 10 =? 2) then mkI I_ANDI rs1p rs1p 0 imm 2
    else if f3 =? 5 then
      let o := Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w 12 12) 11) (Z.shiftl (bitz w 11 11) 4))
                 (Z.shiftl (bitz w 10 9) 8)) (Z.shiftl (bitz w 8 8) 10)) (Z.shiftl (bitz w 7 7) 6))
                 (Z.shiftl (bitz w 6 6) 7)) (Z.shiftl (bitz w 5 3) 1)) (Z.shiftl (bitz w 2 2) 5) in
      mkI I_JAL 0 0 0 (sx o 12) 2
    else if (f3 =? 6) || (f3 =? 7) then
      let o := Z.lor (Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w 12 12) 8) (Z.shiftl (bitz w 11 10) 3))
                 (Z.shiftl (bitz w 6 5) 6)) (Z.shiftl (bitz w 4 3) 1)) (Z.shiftl (bitz w 2 2) 5) in
      mkI (if f3 =? 6 then I_BEQ else I_BNE) 0 rs1p 0 (sx o 9) 2
    else bad
  else if op =? 2 then
    if (f3 =? 0) && (bitz w 12 12 =? 0) then mkI I_SLLI rd rd 0 (bitz w 6 2) 2
    else if f3 =? 0 then mkI I_SLLI rd rd 0 (32 + bitz w 6 2) 2
    else if (f3 =? 4) && (bitz w 12 12 =? 0) && negb (rs2 =? 0) then mkI I_ADD rd 0 rs2 0 2
    else if (f3 =? 4) && (bitz w 12 12 =? 0) && negb (rd =? 0) then mkI I_JALR 0 rd 0 0 2
    else if (f3 =? 4) && negb (bitz w 12 12 =? 0) && negb (rs2 =? 0) then mkI I_ADD rd rd rs2 0 2
    else if (f3 =? 4) && negb (bitz w 12 12 =? 0) && negb (rd =? 0) then mkI I_JALR 1 rd 0 0 2
    else bad
  else bad.

Definition dec32 (w : Z) : ins :=
  let op := Z.land w 127 in let f3 := bitz w 14 12 in let f7 := bitz w 31 25 in
  let rd := bitz w 11 7 in let r1 := bitz w 19 15 in let r2 := bitz w 24 20 in
  let immi := sx (bitz w 31 20) 12 in
  let mk k imm := mkI k rd r1 r2 imm 4 in
  let bad := mk I_BAD 0 in
  if op =? 19 then (* 0x13 *)
    if f3 =? 0 then mk I_ADDI immi
    else if f3 =? 7 then mk I_ANDI immi
    else if (f3 =? 1) && (bitz w 31 26 =? 0) then mk I_SLLI (bitz w 25 20)
    else bad
  else if op =? 51 then (* 0x33 *)
    if (f3 =? 0) && (f7 =? 0) then mk I_ADD 0
    else if (f3 =? 4) && (f7 =? 0) then mk I_XOR 0
    else bad
  else if op =? 55 then mk I_LUI (sx (Z.land w 4294963200) 32)    (* 0x37, w & 0xfffff000 *)
  else if op =? 23 then mk I_AUIPC (sx (Z.land w 4294963200) 32)  (* 0x17 *)
  else if op =? 3 then (if f3 =? 3 then mk I_LD immi else bad)
  else if op =? 35 then (if f3 =? 3 then mk I_SD (sx (Z.lor (Z.shiftl (bitz w 31 25) 5) (bitz w 11 7)) 12) else bad)
  else if op =? 99 then (* 0x63 *)
    let o := sx (Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w 31 31) 12) (Z.shiftl (bitz w 7 7) 11))
                          (Z.shiftl (bitz w 30 25) 5)) (Z.shiftl (bitz w 11 8) 1)) 13 in
    if f3 =? 0 then mk I_BEQ o else if f3 =? 1 then mk I_BNE o
    else if f3 =? 6 then mk I_BLTU o else if f3 =? 7 then mk I_BGEU o else mk I_BAD o
  else if op =? 111 then (* 0x6f *)
    mk I_JAL (sx (Z.lor (Z.lor (Z.lor (Z.shiftl (bitz w 31 31) 20) (Z.shiftl (bitz w 19 12) 12))
                               (Z.shiftl (bitz w 20 20) 11)) (Z.shiftl (bitz w 30 21) 1)) 21)
  else if op =? 103 then (if f3 =? 0 then mk I_JALR immi else bad) (* 0x67 *)
  else bad.

(** [decode(p)]: the four bytes at p; the last two only matter, and are only read, when the low
    two bits of p[0] are 11. *)
Definition cdec (b0 b1 b2 b3 : Z) : ins :=
  let lo := Z.lor b0 (Z.shiftl b1 8) in
  if negb (Z.land lo 3 =? 3) then dec16 lo
  else dec32 (Z.lor lo (Z.lor (Z.shiftl b2 16) (Z.shiftl b3 24))).

(** The 32 bytes of [Ins]. *)
Definition lebytes (n : nat) (v : Z) : list byte := word_to_le_bytes n (Z_to_bv 64 v).
Definition encb (i : ins) : list byte :=
  lebytes 4 (ik i) ++ lebytes 4 (ird i) ++ lebytes 4 (ir1 i) ++ lebytes 4 (ir2 i) ++ lebytes 8 (iimm i) ++ lebytes 4 (ilen i) ++ lebytes 4 0.
