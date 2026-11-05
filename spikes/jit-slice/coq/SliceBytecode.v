(** * Bytecode semantics for one Shen/JIT code object (Shen/JIT Phase 0, spike 4).

    A spike artifact covering only [prim hd], [prim cons] and [return], from
    docs/bytecode.md and src/runtime/value.h.  It stops where the runtime takes over:
    [BRaise] is "call the primitive helper with this argument", and [BCollect] is "call
    the allocator, then restart this instruction". *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope bv_scope.

Definition word := bv 64.

Record bstate := mkB {
  bslots : nat -> word;
  bheap : word -> option word;
  bhp : word;
  bhlimit : word
}.

Inductive binstr :=
| IHd (d s : nat)
| ICons (d a b : nat)
| IRet (s : nat).

Inductive bresult :=
| BReturn (v : word) (st : bstate)
| BRaise (op : Z) (arg : word) (st : bstate)
| BCollect (words : Z) (st : bstate)
| BStuck.

Definition vadd (x : word) (i : Z) : word := Z_to_bv 64 (bv_unsigned x + i).

(** value.h: [tag3], and [TAG_PAIR = 3]. *)
Definition tag3 (x : word) : Z := Z.land (bv_unsigned x) 7.
Definition TAG_PAIR : Z := 3%Z.
(** src/runtime/ops.h: the primitive number the emitter passes for [hd]. *)
Definition P_HD : Z := 11%Z.

Definition set_slot (st : bstate) (d : nat) (v : word) : bstate :=
  mkB (fun k => if Nat.eqb k d then v else bslots st k) (bheap st) (bhp st) (bhlimit st).

(** A pair is two words: head, then tail. *)
Definition heap_cons (st : bstate) (a b : word) : bstate :=
  let p := bhp st in
  mkB (bslots st)
      (fun x => if bool_decide (x = p) then Some a
                else if bool_decide (x = vadd p 8) then Some b
                else bheap st x)
      (vadd p 16) (bhlimit st).

Fixpoint brun (prog : list binstr) (st : bstate) : bresult :=
  match prog with
  | [] => BStuck
  | IHd d s :: rest =>
      let x := bslots st s in
      if Z.eqb (tag3 x) TAG_PAIR then
        match bheap st (vadd x (-3)) with
        | Some v => brun rest (set_slot st d v)
        | None => BStuck
        end
      else BRaise P_HD x st
  | ICons d a b :: rest =>
      if Z.ltb (bv_unsigned (bhlimit st)) (bv_unsigned (bhp st) + 16) then BCollect 2 st
      else
        let va := bslots st a in
        let vb := bslots st b in
        let p := bhp st in
        brun rest (set_slot (heap_cons st va vb) d (vadd p TAG_PAIR))
  | IRet s :: _ => BReturn (bslots st s) st
  end.

(** (code sl.f 2 6 () ((prim 4 hd 2) (prim 5 cons 4 3) (return 5)) () ()) *)
Definition slice_prog : list binstr := [IHd 4 2; ICons 5 4 3; IRet 5].
