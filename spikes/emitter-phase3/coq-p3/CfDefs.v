(** * A function-level checker of emitted RV64 against bytecode (Shen/JIT Phase 0, spike 8).

    The checker takes no analysis from the emitter.  For each bytecode instruction it
    symbolically runs that instruction's machine code from a canonical state and compares the
    result with what the bytecode requires.  The only inputs from outside are:
    - [cut]: the byte offset of each instruction,
    - [inv]: the canonical state before each instruction (what is in CACHE, which slots are current
      in the frame, which are known pairs, how much room is reserved).
    Both are certificates: a wrong one makes the check fail.  [CfSound] holds the theorem.

    A spike artifact: the bytecode here is a subset of docs/bytecode.md, with a test and its
    jump-if-false as one instruction, and it isn't connected to Búri's KLambda semantics. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec CatExec SeqExec StepTac WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Definition word := bv 64.

(* ------------------------------------------------------------------ *)
(* Bytecode                                                            *)
(* ------------------------------------------------------------------ *)

Inductive opnd := OSlot (n : Z) | OConst (i : Z).

Inductive binstr :=
| IMove (d : Z) (o : opnd)
| ICons (d : Z) (a b : opnd)
| IHd (d x : Z)
| ITl (d x : Z)
| IEqJf (t : Z) (a b : opnd) (l : Z)   (* (prim t = a b) (jump-if-false t l) *)
| IConspJf (t x : Z) (l : Z)           (* (prim t cons? x) (jump-if-false t l) *)
| ILabel (l : Z)
| IJump (l : Z)
| IRet (o : opnd)
| ICallS (d a n k : Z).                (* spike 9: (call-sealed d a k n), the callee in constant k *)

Record bstate := mkB {
  bslots : Z -> word;
  bconsts : Z -> word;
  bheap : word -> option word;
  bhp : word;
  bhlimit : word
}.

Definition opval (st : bstate) (o : opnd) : word :=
  match o with OSlot n => bslots st n | OConst i => bconsts st i end.

Definition set_slot (st : bstate) (d : Z) (v : word) : bstate :=
  mkB (fun k => if Z.eqb k d then v else bslots st k) (bconsts st) (bheap st) (bhp st) (bhlimit st).

(** value.h: [tag3], and [TAG_PAIR = 3]. *)
Definition tag3 (x : word) : Z := Z.land (bv_unsigned x) 7.

Definition heap_cons (st : bstate) (d : Z) (a b : word) : bstate :=
  let p := bhp st in
  mkB (fun k => if Z.eqb k d then v_addi p 3 else bslots st k) (bconsts st)
      (fun x => if bool_decide (x = p) then Some a
                else if bool_decide (x = v_addi p 8) then Some b
                else bheap st x)
      (v_addi p 16) (bhlimit st).

Fixpoint find_label (p : list binstr) (l : Z) (i : nat) : option nat :=
  match p with
  | [] => None
  | ILabel l' :: r => if Z.eqb l l' then Some i else find_label r l (S i)
  | _ :: r => find_label r l (S i)
  end.

Inductive bres :=
| BNext (i : nat) (st : bstate)
| BReturn (v : word) (st : bstate)
| BCall (d a n k : Z) (st : bstate)   (* spike 9: a call; what it returns is the callee's, by its contract *)
| BOther.   (* a raise, or a jump to no label; an accepted function doesn't reach it *)

Section Bytecode.
Variable keq : word -> word -> bool.  (* the kernel's = *)
Variables vtrue vfalse : word.

Definition bnext (p : list binstr) (i : nat) (st : bstate) : bres :=
  match nth_error p i with
  | None => BOther
  | Some ins =>
    match ins with
    | IMove d o => BNext (S i) (set_slot st d (opval st o))
    | ICons d a b => BNext (S i) (heap_cons st d (opval st a) (opval st b))
    | IHd d x =>
        if Z.eqb (tag3 (bslots st x)) 3 then
          match bheap st (v_addi (bslots st x) (-3)) with
          | Some v => BNext (S i) (set_slot st d v)
          | None => BOther
          end
        else BOther
    | ITl d x =>
        if Z.eqb (tag3 (bslots st x)) 3 then
          match bheap st (v_addi (bslots st x) 5) with
          | Some v => BNext (S i) (set_slot st d v)
          | None => BOther
          end
        else BOther
    | IEqJf t a b l =>
        if keq (opval st a) (opval st b) then BNext (S i) (set_slot st t vtrue)
        else match find_label p l 0 with
             | Some li => BNext li (set_slot st t vfalse)
             | None => BOther
             end
    | IConspJf t x l =>
        if Z.eqb (tag3 (bslots st x)) 3 then BNext (S i) (set_slot st t vtrue)
        else match find_label p l 0 with
             | Some li => BNext li (set_slot st t vfalse)
             | None => BOther
             end
    | ILabel _ => BNext (S i) st
    | IJump l => match find_label p l 0 with Some li => BNext li st | None => BOther end
    | IRet o => BReturn (opval st o) st
    | ICallS d a n k => BCall d a n k st
    end
  end.
End Bytecode.

(* ------------------------------------------------------------------ *)
(* Abstract values                                                     *)
(* ------------------------------------------------------------------ *)

Inductive base :=
| KConst | KSlot (n : Z) | KFp | KVm | KHp | KHlim | KHd (n : Z) | KTl (n : Z)
| KCell (i : Z) | KStatus | KCount
| KEnt (i : Z).   (* spike 9: the entry word of the procedure in constant i *)

Inductive aval := Lin (b : base) (k : Z) | TagOf (n : Z) | Unk.

Definition base_eqb (x y : base) : bool :=
  match x, y with
  | KConst, KConst | KFp, KFp | KVm, KVm | KHp, KHp | KHlim, KHlim | KStatus, KStatus | KCount, KCount => true
  | KSlot a, KSlot b | KHd a, KHd b | KTl a, KTl b | KCell a, KCell b | KEnt a, KEnt b => Z.eqb a b
  | _, _ => false
  end.

(** Syntactic equality; [Unk] equals nothing. *)
Definition same (x y : aval) : bool :=
  match x, y with
  | Lin a j, Lin b k => base_eqb a b && Z.eqb j k
  | TagOf a, TagOf b => Z.eqb a b
  | _, _ => false
  end.

Record env := mkE { e_st : bstate; e_fp : word; e_vm : word; e_status : word; e_count : word }.

Definition base_val (e : env) (b : base) : word :=
  match b with
  | KConst => Z_to_bv 64 0
  | KSlot n => bslots (e_st e) n
  | KFp => e_fp e
  | KVm => e_vm e
  | KHp => bhp (e_st e)
  | KHlim => bhlimit (e_st e)
  | KHd n => match bheap (e_st e) (v_addi (bslots (e_st e) n) (-3)) with Some v => v | None => Z_to_bv 64 0 end
  | KTl n => match bheap (e_st e) (v_addi (bslots (e_st e) n) 5) with Some v => v | None => Z_to_bv 64 0 end
  | KCell i => bconsts (e_st e) i
  | KStatus => e_status e
  | KCount => e_count e
  | KEnt i => match bheap (e_st e) (v_addi (bconsts (e_st e) i) 3) with Some v => v | None => Z_to_bv 64 0 end
  end.

Definition eval (e : env) (a : aval) : word :=
  match a with
  | Lin b k => v_addi (base_val e b) k
  | TagOf n => alu64 ALU_AND (v_addi (bslots (e_st e) n) (-3)) (sext 64 (7 : bv 12))
  | Unk => Z_to_bv 64 0
  end.

Definition known (a : aval) : bool := match a with Unk => false | _ => true end.

Definition mkc (z : Z) : aval := Lin KConst (bv_wrap 64 z).

Definition add_k (a : aval) (i : Z) : aval :=
  match a with
  | Lin KConst k => mkc (k + i)
  | Lin b k => Lin b (k + i)
  | _ => Unk
  end.

(* ------------------------------------------------------------------ *)
(* The configuration of one function                                   *)
(* ------------------------------------------------------------------ *)

Inductive ckind := KImm (w : Z) | KPtr (addr : Z) (tag : Z).

Record cfg := mkC {
  cbase : Z;
  cbytes : list Z;
  cframe : Z;
  ckinds : Z -> option ckind;
  h_alloc : Z;
  c_unwind : Z;
  c_arity_stub : Z;
  c_arity : Z
}.

Definition at_ (c : cfg) (o : Z) : word := Z_to_bv 64 (cbase c + o).
Definition code_len (c : cfg) : Z := Z.of_nat (length (cbytes c)).
Definition code_byte (c : cfg) (i : Z) : byte := Z_to_bv 8 (nth (Z.to_nat i) (cbytes c) 0%Z).
Definition code_word (c : cfg) (o : Z) : bv 32 :=
  le4 (code_byte c (o + 3)) (code_byte c (o + 2)) (code_byte c (o + 1)) (code_byte c o).

(** Registers a block may write. s1 and the callee-saved registers above s5 are not among them.
    Spike 9: s4 and s5 (x20, x21) are 0.4's kept registers; JIT code clobbers them, and [jit_call] saves them.
    s0, the frame pointer, moves up by a call's window and back: every way out of a block checks it
    (post_ok, check_slow, check_resume, the return, the call), so a block may write it. *)
Definition scratch (r : Z) : bool :=
  match r with
  | 1 | 5 | 6 | 7 | 8 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 28 | 29 | 30 | 31 => true
  | _ => false
  end%Z.

Record Y := mkY {
  yA : Z -> aval;   (* registers *)
  yF : Z -> aval;   (* what each frame slot holds *)
  yH : Z -> aval;   (* what each new word at HP + k holds *)
  yV : Z -> aval;   (* what the VM's fields hold *)
  yroom : Z         (* bytes known free at HP *)
}.

Definition upd (f : Z -> aval) (k : Z) (v : aval) : Z -> aval :=
  fun x => if Z.eqb x k then v else f x.

Definition setr (y : Y) (r : Z) (v : aval) : Y :=
  mkY (upd (yA y) r v) (yF y) (yH y) (yV y) (yroom y).

(** What a load from an abstract address gives; [None] if the address isn't known readable. *)
Definition load (c : cfg) (st_P : Z) (y : Y) (a : aval) : option aval :=
  match a with
  | Lin KFp k =>
      if (Z.leb 0 k && Z.ltb k (8 * cframe c) && Z.eqb (k mod 8) 0)%bool then
        if known (yF y (k / 8)) then Some (yF y (k / 8)) else None
      else None
  | Lin KVm k =>
      if (Z.eqb k 0 || Z.eqb k 8)%bool then
        if known (yV y k) then Some (yV y k) else None
      else None
  | Lin (KSlot x) k =>
      if (Z.leb 0 x && Z.ltb x 64 && Z.testbit st_P x)%bool then
        if Z.eqb k (-3) then Some (Lin (KHd x) 0)
        else if Z.eqb k 5 then Some (Lin (KTl x) 0)
        else None
      else None
  | Lin KConst k =>
      None
  | Lin (KCell i) k =>
      (* spike 9: PROC_ENTRY of a procedure constant, at offset 8 - TAG_PROC *)
      if Z.eqb k 3 then
        match ckinds c i with Some (KPtr _ t) => if Z.eqb t 5 then Some (Lin (KEnt i) 0) else None | _ => None end
      else None
  | _ => None
  end.

Definition store (c : cfg) (y : Y) (a v : aval) : option Y :=
  match a with
  | Lin KFp k =>
      if (Z.leb 0 k && Z.ltb k (8 * cframe c) && Z.eqb (k mod 8) 0)%bool then
        Some (mkY (yA y) (upd (yF y) (k / 8) v) (yH y) (yV y) (yroom y))
      else None
  | Lin KHp k =>
      if (Z.leb 0 k && Z.leb (k + 8) (yroom y) && Z.eqb (k mod 8) 0)%bool then
        Some (mkY (yA y) (yF y) (upd (yH y) k v) (yV y) (yroom y))
      else None
  | Lin KVm k =>
      if (Z.eqb k 0 || Z.eqb k 16 || Z.eqb k 24)%bool then
        Some (mkY (yA y) (yF y) (yH y) (upd (yV y) k v) (yroom y))
      else None
  | _ => None
  end.

Inductive res :=
| RDone (y : Y)
| RJump (t : Z) (y : Y)
| RRet (y : Y)
| RCall (callee next : Z) (y : Y)
| RIJump (a : aval) (y : Y)   (* spike 9: a jump to a procedure's entry *)
| RBr (cc : branch_cond) (a b : aval) (t : Z) (y : Y) (rest : res).

Definition in_code (c : cfg) (o : Z) : bool :=
  (Z.leb 0 o && Z.leb (o + 4) (code_len c) && Z.eqb (o mod 2) 0)%bool.

(** A branch not taken can prove room. *)
Definition note_room (cc : branch_cond) (a b : aval) (y : Y) : Y :=
  match cc, a, b with
  | BC_LTU, Lin KHlim 0, Lin KHp k =>
      if (Z.leb 0 k && Z.leb k 4096)%bool then mkY (yA y) (yF y) (yH y) (yV y) k else y
  | _, _, _ => y
  end.

Definition aval_add (a b : aval) : aval :=
  match a with
  | Lin KConst k => add_k b k
  | _ => match b with Lin KConst k => add_k a k | _ => Unk end
  end.

Definition const_op (f : word -> word) (a : aval) : aval :=
  match a with
  | Lin KConst k => Lin KConst (bv_unsigned (f (Z_to_bv 64 k)))
  | _ => Unk
  end.

Definition aval_and (a : aval) (imm : Z) : aval :=
  match a with
  | Lin (KSlot n) k => if (Z.eqb k (-3) && Z.eqb imm 7)%bool then TagOf n else Unk
  | _ => Unk
  end.

Definition aval_xor (a b : aval) : aval :=
  match a, b with
  | Lin KConst j, Lin KConst k =>
      Lin KConst (bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 j) (Z_to_bv 64 k)))
  | _, _ => Unk
  end.

(** Constant cells: [cell_of k] is the constant whose cell is at address [k]. *)
Section Run.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable st_P : Z.

Definition load' (y : Y) (a : aval) : option aval :=
  match a with
  | Lin KConst k =>
      match cell_of k with
      | Some i => match ckinds c i with
                  | Some (KPtr addr _) => if Z.eqb addr k then Some (Lin (KCell i) 0) else None
                  | _ => None
                  end
      | None => None
      end
  | _ => load c st_P y a
  end.

Definition wr (y : Y) (rd : reg) (v : aval) (k : Y -> option res) : option res :=
  if (negb (is_x0 rd) && scratch (bv_unsigned rd))%bool then k (setr y (bv_unsigned rd) v) else None.

Fixpoint run (fuel : nat) (o stop : Z) (y : Y) {struct fuel} : option res :=
  match fuel with
  | O => None
  | S f =>
    if Z.eqb o stop then Some (RDone y) else
    if negb (in_code c o) then None else
    let w := code_word c o in
    if is_ecall w then None else
    match decode_any w with
    | None => None
    | Some (i, sz) =>
      match i with
      | OpImm ALU_ADD rd rs imm =>
          wr y rd (add_k (yA y (bv_unsigned rs)) (bv_signed imm)) (run f (o + sz) stop)
      | OpImm ALU_AND rd rs imm =>
          wr y rd (aval_and (yA y (bv_unsigned rs)) (bv_signed imm)) (run f (o + sz) stop)
      | Op ALU_ADD rd rs1 rs2 =>
          wr y rd (aval_add (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2))) (run f (o + sz) stop)
      | Op ALU_XOR rd rs1 rs2 =>
          wr y rd (aval_xor (yA y (bv_unsigned rs1)) (yA y (bv_unsigned rs2))) (run f (o + sz) stop)
      | ShiftImm ALU_SLL rd rs sh =>
          wr y rd (const_op (fun x => alu64 ALU_SLL x (zext 64 sh)) (yA y (bv_unsigned rs))) (run f (o + sz) stop)
      | Lui rd imm =>
          wr y rd (Lin KConst (bv_unsigned (v_lui (Z.shiftl (bv_signed imm) 12)))) (run f (o + sz) stop)
      | Auipc rd imm =>
          wr y rd (Lin KConst (bv_unsigned (v_auipc (at_ c o) (Z.shiftl (bv_signed imm) 12)))) (run f (o + sz) stop)
      | Load SZ8 true rd rs imm =>
          match load' y (add_k (yA y (bv_unsigned rs)) (bv_signed imm)) with
          | Some v => wr y rd v (run f (o + sz) stop)
          | None => None
          end
      | Store SZ8 rs1 rs2 imm =>
          match store c y (add_k (yA y (bv_unsigned rs1)) (bv_signed imm)) (yA y (bv_unsigned rs2)) with
          | Some y' => run f (o + sz) stop y'
          | None => None
          end
      | Branch cc rs1 rs2 imm =>
          let a := yA y (bv_unsigned rs1) in
          let b := yA y (bv_unsigned rs2) in
          if (known a && known b)%bool then
            match run f (o + sz) stop (note_room cc a b y) with
            | Some r => Some (RBr cc a b (o + bv_signed imm) y r)
            | None => None
            end
          else None
      | Jal rd imm =>
          if is_x0 rd then Some (RJump (o + bv_signed imm) y)
          else if Z.eqb (bv_unsigned rd) 1 then
            Some (RCall (cbase c + o + bv_signed imm) (o + sz) (setr y 1 (mkc (cbase c + (o + sz)))))
          else None
      | Jalr rd rs imm =>
          if is_x0 rd then
            match yA y (bv_unsigned rs) with
            | Lin (KSlot 0) 0 => if Z.eqb (bv_signed imm) 0 then Some (RRet y) else None
            | Lin (KEnt i) 0 => if Z.eqb (bv_signed imm) 0 then Some (RIJump (Lin (KEnt i) 0) y) else None
            | _ => None
            end
          else if Z.eqb (bv_unsigned rd) 1 then
            match yA y (bv_unsigned rs) with
            | Lin KConst k =>
                Some (RCall (bv_unsigned (jalr_tgt (Z_to_bv 64 k) (bv_signed imm))) (o + sz)
                       (setr y 1 (mkc (cbase c + (o + sz)))))
            | _ => None
            end
          else None
      | _ => None
      end
    end
  end.
End Run.

(* ------------------------------------------------------------------ *)
(* Canonical states and the check of each instruction                  *)
(* ------------------------------------------------------------------ *)

Record CS := mkS { sC : option Z; sM : Z; sP : Z; sR : Z; sK0 : option Z; sK1 : option Z }.

Definition optslot (o : option Z) : aval := match o with Some n => Lin (KSlot n) 0 | None => Unk end.

Definition frame0 (s : CS) (n : Z) : aval :=
  if (Z.leb 0 n && Z.ltb n 64 && Z.testbit (sM s) n)%bool then Lin (KSlot n) 0 else Unk.

Definition y0 (s : CS) : Y :=
  mkY (fun r => if Z.eqb r 0 then Lin KConst 0
                else if Z.eqb r 8 then Lin KFp 0
                else if Z.eqb r 9 then Lin KVm 0
                else if Z.eqb r 18 then match sC s with Some n => Lin (KSlot n) 0 | None => Unk end
                else if Z.eqb r 19 then Lin KHp 0
                else if Z.eqb r 20 then optslot (sK0 s)
                else if Z.eqb r 21 then optslot (sK1 s)
                else Unk)
      (frame0 s)
      (fun _ => Unk)
      (fun k => if Z.eqb k 8 then Lin KHlim 0 else Unk)
      (8 * sR s).

(** After a call to the allocator: only FP, VM and the status register are known, and the VM holds the
    heap pointer and limit. *)
Definition y_after (s : CS) : Y :=
  mkY (fun r => if Z.eqb r 0 then Lin KConst 0
                else if Z.eqb r 8 then Lin KFp 0
                else if Z.eqb r 9 then Lin KVm 0
                else if Z.eqb r 10 then Lin KStatus 0
                else Unk)
      (frame0 s)
      (fun _ => Unk)
      (fun k => if Z.eqb k 8 then Lin KHlim 0 else if Z.eqb k 0 then Lin KHp 0 else Unk)
      0.

Definition slots64 : list Z := map Z.of_nat (seq 0 64).

(** Spike 9: what a call leaves known.  The callee owns slots [a] and up; CACHE, the kept registers,
    the pair facts and the reserved room are dropped. *)
Definition after_call (s : CS) (a : Z) : CS := mkS None (Z.land (sM s) (Z.ones a)) 0 0 None None.

(** On return: the callee's frame pointer, the value in a0, the heap pointer in s3. *)
Definition y_ret (s : CS) (a : Z) : Y :=
  mkY (fun r => if Z.eqb r 0 then Lin KConst 0
                else if Z.eqb r 8 then Lin KFp (8 * a)
                else if Z.eqb r 9 then Lin KVm 0
                else if Z.eqb r 10 then Lin KStatus 0
                else if Z.eqb r 19 then Lin KHp 0
                else Unk)
      (frame0 s)
      (fun _ => Unk)
      (fun k => if Z.eqb k 8 then Lin KHlim 0 else Unk)
      0.

(** The frame still holds every slot [s] says is current. *)
Definition frame_kept (s : CS) (y : Y) : bool :=
  forallb (fun n => negb (Z.testbit (sM s) n) || same (yF y n) (Lin (KSlot n) 0)) slots64.

(** Spike 9: the same, except the two words a call writes at its window. *)
Definition frame_kept_call (s : CS) (a : Z) (y : Y) : bool :=
  forallb (fun n => negb (Z.testbit (sM s) n) || Z.eqb n a || Z.eqb n (a + 1) || same (yF y n) (Lin (KSlot n) 0)) slots64.

Definition nats (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Definition same_opt_d (d : option Z) (n : Z) : bool :=
  match d with Some x => Z.eqb x n | None => false end.

(** What a register holds after a block, against the slot the next state says it holds (spike 9:
    CACHE and the two kept registers alike). *)
Definition reg_post (d : option Z) (v : aval) (y : Y) (r : Z) (o : option Z) : bool :=
  match o with
  | None => true
  | Some n => if same_opt_d d n then same (yA y r) v else same (yA y r) (Lin (KSlot n) 0)
  end.

(** The state [t] holds after a block that gave slot [d] the value [v] and moved HP by [delta].
    A slot that isn't known current is just left out of [t]: nothing can read it. *)
Definition post_ok (c : cfg) (s : CS) (y : Y) (d : option Z) (v : aval) (delta : Z) (plus : Z) (t : CS) : bool :=
  same (yA y 8) (Lin KFp 0) && same (yA y 9) (Lin KVm 0) && same (yA y 19) (Lin KHp delta) &&
  reg_post d v y 18 (sC t) && reg_post d v y 20 (sK0 t) && reg_post d v y 21 (sK1 t) &&
  forallb (fun n =>
    negb (Z.testbit (sM t) n) ||
    (Z.ltb n (cframe c) &&
     (if same_opt_d d n then same (yF y n) v else same (yF y n) (Lin (KSlot n) 0))))
    slots64 &&
  forallb (fun n =>
    negb (Z.testbit (sP t) n) ||
    (negb (same_opt_d d n) && (Z.testbit (sP s) n || Z.eqb n plus)))
    slots64 &&
  Z.leb 0 (sR t) && Z.leb (8 * sR t + delta) (yroom y).

Definition abs_op (c : cfg) (o : opnd) : aval :=
  match o with
  | OSlot n => Lin (KSlot n) 0
  | OConst i =>
      match ckinds c i with
      | Some (KImm w) => Lin KConst w
      | Some (KPtr _ _) => Lin (KCell i) 0
      | None => Unk
      end
  end.

(** value.h: a constant [=] can compare by identity. *)
Definition identity_tag (t : Z) : bool := Z.eqb t 6 || Z.eqb t 2 || Z.eqb t 5.

Definition identity_op (c : cfg) (o : opnd) : bool :=
  match o with
  | OConst i =>
      match ckinds c i with
      | Some (KImm w) => identity_tag (Z.land w 7)
      | Some (KPtr _ t) => identity_tag t
      | None => false
      end
  | OSlot _ => false
  end.

Section Check.
Variable c : cfg.
Variable cell_of : Z -> option Z.
Variable p : list binstr.
Variable cut : nat -> Z.
Variable inv : nat -> option CS.
Variable fuel : nat.

Definition post_at (s : CS) (y : Y) (d : option Z) (v : aval) (delta plus : Z) (j : nat) : bool :=
  match inv j with Some t => post_ok c s y d v delta plus t | None => false end.

(** A later instruction that a jump to label [l] reaches: it has to be forward of [i]. *)
Definition target (i : nat) (l : Z) (t : Z) : option nat :=
  match find_label p l 0 with
  | Some li => if (Nat.ltb i li && Z.eqb (cut li) t)%bool then Some li else None
  | None => None
  end.

(** The slow path of an allocation: publish, call the allocator, and come back to the instruction. *)
Definition check_resume (s : CS) (i : nat) (next : Z) : bool :=
  match run c cell_of (sP s) fuel next (-1) (y_after s) with
  | Some (RBr BC_EQ a b t _ (RJump back y)) =>
      same a (Lin KStatus 0) && same b (mkc 26) && Z.eqb (cbase c + t) (c_unwind c) &&
      Z.eqb back (cut i) && Z.eqb (sR s) 0 && frame_kept s y &&
      same (yA y 8) (Lin KFp 0) && same (yA y 9) (Lin KVm 0) && same (yA y 19) (Lin KHp 0) &&
      reg_post None Unk y 18 (sC s) && reg_post None Unk y 20 (sK0 s) && reg_post None Unk y 21 (sK1 s)
  | _ => false
  end.

Definition check_slow (s : CS) (i : nat) (y : Y) (t : Z) (words : Z) : bool :=
  match run c cell_of (sP s) fuel t (-1) y with
  | Some (RCall callee next y') =>
      Z.eqb callee (h_alloc c) &&
      same (yV y' 16) (Lin KFp 0) &&
      same (yV y' 24) (Lin KFp (8 * cframe c)) &&
      same (yV y' 0) (Lin KHp 0) &&
      same (yA y' 10) (Lin KVm 0) &&
      same (yA y' 11) (mkc words) &&
      same (yA y' 8) (Lin KFp 0) && same (yA y' 9) (Lin KVm 0) &&
      same (yA y' 19) (Lin KHp 0) && frame_kept s y' &&
      check_resume s i next
  | _ => false
  end.

Definition cons_post (s : CS) (i : nat) (y : Y) (d : Z) (a b : opnd) : bool :=
  known (abs_op c a) && known (abs_op c b) &&
  same (yH y 0) (abs_op c a) && same (yH y 8) (abs_op c b) &&
  post_at s y (Some d) (Lin KHp 3) 16 (-1) (S i).

Definition check_at (i : nat) : bool :=
  match inv i with
  | None => true
  | Some s =>
    match nth_error p i with
    | None => false
    | Some ins =>
      let from := cut i in
      let to := cut (S i) in
      let go := run c cell_of (sP s) fuel from to (y0 s) in
      match ins with
      | IMove d o =>
          match go with
          | Some (RDone y) => known (abs_op c o) && post_at s y (Some d) (abs_op c o) 0 (-1) (S i)
          | _ => false
          end
      | IHd d x =>
          (Z.leb 0 x && Z.ltb x 64 && Z.testbit (sP s) x)%bool &&
          match go with
          | Some (RDone y) => post_at s y (Some d) (Lin (KHd x) 0) 0 (-1) (S i)
          | _ => false
          end
      | ITl d x =>
          (Z.leb 0 x && Z.ltb x 64 && Z.testbit (sP s) x)%bool &&
          match go with
          | Some (RDone y) => post_at s y (Some d) (Lin (KTl x) 0) 0 (-1) (S i)
          | _ => false
          end
      | ICons d a b =>
          match go with
          | Some (RDone y) => Z.leb 2 (sR s) && cons_post s i y d a b
          | Some (RBr BC_LTU la lb t y1 (RDone y)) =>
              match lb with
              | Lin KHp k =>
                  same la (Lin KHlim 0) && Z.leb 16 k && Z.leb k 4096 && Z.eqb (k mod 8) 0 &&
                  Z.eqb (sR s) 0 &&
                  check_slow s i y1 t (k / 8) &&
                  cons_post s i y d a b
              | _ => false
              end
          | _ => false
          end
      | IEqJf tv a b l =>
          (identity_op c a || identity_op c b) &&
          match go with
          | Some (RBr BC_NE x w t y1 (RDone y)) =>
              ((same x (abs_op c a) && same w (abs_op c b)) || (same x (abs_op c b) && same w (abs_op c a))) &&
              match target i l t with
              | Some li => post_at s y1 (Some tv) Unk 0 (-1) li && post_at s y (Some tv) Unk 0 (-1) (S i)
              | None => false
              end
          | _ => false
          end
      | IConspJf tv x l =>
          (Z.leb 0 x && Z.ltb x 64)%bool &&
          match go with
          | Some (RBr BC_NE w z t y1 (RDone y)) =>
              same w (TagOf x) && same z (Lin KConst 0) &&
              match target i l t with
              | Some li => post_at s y1 (Some tv) Unk 0 (-1) li && post_at s y (Some tv) Unk 0 x (S i)
              | None => false
              end
          | _ => false
          end
      | ILabel _ =>
          Z.eqb from to && post_at s (y0 s) None Unk 0 (-1) (S i)
      | IJump l =>
          match go with
          | Some (RJump t y) =>
              match target i l t with Some li => post_at s y None Unk 0 (-1) li | None => false end
          | Some (RDone y) =>
              match target i l to with Some li => post_at s y None Unk 0 (-1) li | None => false end
          | _ => false
          end
      | ICallS d a n k =>
          (* spike 9: arguments current in slots a + 2 and up; the call writes the return address at
             slot a and the callee at a + 1, moves FP up by a slots and jumps to the entry; the code
             at the return address moves FP back and keeps the result. *)
          (Z.leb 2 a && Z.leb 0 n && Z.leb (a + 2 + n) (cframe c) && Z.eqb (sR s) 0)%bool &&
          match ckinds c k with Some (KPtr _ t) => Z.eqb t 5 | _ => false end &&
          forallb (fun j => Z.testbit (sM s) (a + 2 + j)) (nats n) &&
          match run c cell_of (sP s) fuel from (-1) (y0 s) with
          | Some (RIJump (Lin (KEnt k') 0) y) =>
              Z.eqb k' k && same (yF y (a + 1)) (Lin (KCell k) 0) &&
              same (yA y 8) (Lin KFp (8 * a)) && same (yA y 9) (Lin KVm 0) && same (yA y 19) (Lin KHp 0) &&
              same (yA y 11) (Lin (KCell k) 0) && same (yA y 12) (mkc n) &&
              (Z.eqb n 0 || same (yA y 18) (Lin (KSlot (a + 2)) 0))%bool &&
              frame_kept_call s a y &&
              match yF y a with
              | Lin KConst ra =>
                  (* the return address scans as a fixnum, and lies in this code *)
                  Z.eqb (ra mod 4) 0 && in_code c (ra - cbase c) &&
                  match run c cell_of 0 fuel (ra - cbase c) to (y_ret (after_call s a) a) with
                  | Some (RDone y2) => post_at (after_call s a) y2 (Some d) (Lin KStatus 0) 0 (-1) (S i)
                  | _ => false
                  end
              | _ => false
              end
          | _ => false
          end
      | IRet o =>
          match go with
          | Some (RRet y) =>
              known (abs_op c o) && same (yA y 10) (abs_op c o) && same (yA y 19) (Lin KHp 0) &&
              same (yA y 8) (Lin KFp 0) && same (yA y 9) (Lin KVm 0)
          | _ => false
          end
      end
    end
  end.

(** Every instruction, and one past the end, where [inv] must be [None]: nothing falls off the end. *)
Definition check_all : bool :=
  forallb check_at (seq 0 (S (length p))).

(** Entry: the argument count, then the first instruction. *)
Definition check_entry (first : Z) (s : CS) : bool :=
  let y := match y0 s with
           | mkY a f h v r => mkY (upd a 12 (Lin KCount 0)) f h v r
           end in
  match run c cell_of (sP s) fuel 0 first y with
  | Some (RBr BC_NE a b t _ (RDone y')) =>
      same a (Lin KCount 0) && same b (mkc (c_arity c)) && Z.eqb (cbase c + t) (c_arity_stub c) &&
      Z.eqb first (cut 0) &&
      match inv 0 with Some t0 => post_ok c s y' None Unk 0 (-1) t0 | None => false end
  | _ => false
  end.
End Check.

(* ------------------------------------------------------------------ *)
(* Reading the bytecode words the JIT compiled (src/runtime/ops.h)     *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.
Definition OPF : Z := 2147483648.
Definition mk_opnd (w : Z) : opnd := if Z.leb OPF w then OConst (w - OPF) else OSlot w.

Record prims := mkP { p_eq : Z; p_cons : Z; p_hd : Z; p_tl : Z; p_consp : Z }.

(** Each instruction with its word offset.  A [=] or [cons?] whose result the next [jump-if-false]
    tests is one instruction, as the JIT compiles them. *)
Fixpoint parse (pr : prims) (fuel : nat) (ws : list Z) (off : nat) : option (list (nat * binstr)) :=
  match fuel with
  | O => None
  | S f =>
    match ws with
    | [] => Some []
    | 0 :: d :: s :: r => option_map (cons (off, IMove d (mk_opnd s))) (parse pr f r (off + 3))
    | 1 :: d :: k :: r => option_map (cons (off, IMove d (OConst k))) (parse pr f r (off + 3))
    | 5 :: l :: r => option_map (cons (off, ILabel l)) (parse pr f r (off + 2))
    | 6 :: l :: r => option_map (cons (off, IJump l)) (parse pr f r (off + 2))
    | 14 :: s :: r => option_map (cons (off, IRet (mk_opnd s))) (parse pr f r (off + 2))
    | 9 :: d :: a :: k :: n :: r => option_map (cons (off, ICallS d a n k)) (parse pr f r (off + 5))
    | 4 :: d :: q :: 2 :: a :: b :: 7 :: t :: l :: r =>
        if (Z.eqb q (p_eq pr) && Z.eqb t d)%bool then
          option_map (cons (off, IEqJf d (mk_opnd a) (mk_opnd b) l)) (parse pr f r (off + 9))
        else if Z.eqb q (p_cons pr) then
          option_map (cons (off, ICons d (mk_opnd a) (mk_opnd b))) (parse pr f (7 :: t :: l :: r) (off + 6))
        else None
    | 4 :: d :: q :: 1 :: x :: 7 :: t :: l :: r =>
        if (Z.eqb q (p_consp pr) && Z.eqb t d && Z.leb x OPF)%bool then
          option_map (cons (off, IConspJf d x l)) (parse pr f r (off + 8))
        else if (Z.eqb q (p_hd pr) && Z.ltb x OPF)%bool then
          option_map (cons (off, IHd d x)) (parse pr f (7 :: t :: l :: r) (off + 5))
        else if (Z.eqb q (p_tl pr) && Z.ltb x OPF)%bool then
          option_map (cons (off, ITl d x)) (parse pr f (7 :: t :: l :: r) (off + 5))
        else None
    | 4 :: d :: q :: 2 :: a :: b :: r =>
        if Z.eqb q (p_cons pr) then
          option_map (cons (off, ICons d (mk_opnd a) (mk_opnd b))) (parse pr f r (off + 6))
        else None
    | 4 :: d :: q :: 1 :: x :: r =>
        if (Z.eqb q (p_hd pr) && Z.ltb x OPF)%bool then option_map (cons (off, IHd d x)) (parse pr f r (off + 5))
        else if (Z.eqb q (p_tl pr) && Z.ltb x OPF)%bool then option_map (cons (off, ITl d x)) (parse pr f r (off + 5))
        else None
    | _ => None
    end
  end.
