(** * [run_block] and its inlined [load], [setr] and [add_k] (overlay/check_fn.c), transcribed into Rocq.

    The state is the C's: [AV] as three integers (k as the unsigned image of the i64), [Sym] as its
    32 registers and up to 16 recorded stores, [Run] as the recorded branches.  [rb_iter] is one
    trip of the loop for the instruction at [o]; [crun] is the loop with its fuel.  Forms this spike
    doesn't prove on the binary give [IOut]; the binary theorem assumes none is reached. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Examples.s9bin_ns Require Import DecSpec.
Import ListNotations.
Open Scope Z_scope.

Definition W64 (z : Z) : Z := z mod 2 ^ 64.
Definition signed64 (z : Z) : Z := bv_swrap 64 z.

(** enum base *)
Definition B_UNK := 0. Definition B_CONST := 1. Definition B_SLOT := 2. Definition B_FP := 3.
Definition B_VM := 4. Definition B_HP := 5. Definition B_HLIM := 6. Definition B_RET := 7.
Definition B_HD := 8. Definition B_TL := 9. Definition B_CELL := 10. Definition B_TAG := 13.

Record av := AV { avb : Z; ava : Z; avk : Z }.
Definition UNK := AV 0 0 0.

Definition same (x y : av) : bool :=
  negb (avb x =? B_UNK) && (avb x =? avb y) && (ava x =? ava y) && (avk x =? avk y).

Definition add_k (x : av) (k : Z) : av :=
  if (avb x =? B_UNK) || (avb x =? B_TAG) then UNK else AV (avb x) (ava x) (W64 (avk x + k)).

Record sym := Sym { yr : Z -> av; yw : Z -> av * av; ynw : Z }.

Definition upd {A} (f : Z -> A) (k : Z) (v : A) : Z -> A := fun x => if x =? k then v else f x.

Definition setr (y : sym) (rd : Z) (v : av) : sym :=
  if rd =? 0 then y else Sym (upd (yr y) rd v) (yw y) (ynw y).

(** What the loop reads of the context and the canonical state. *)
Record env := Env {
  e_len : Z; e_hp : Z; e_hlim : Z; e_cells : list Z;  (* the cell addresses, nconst of them *)
  e_M : Z; e_P : Z }.

(** The store log, newest first: [for (i = nw - 1; i >= 0; i--) if (same(w[i].a, a)) return w[i].v]. *)
Fixpoint find_store (w : Z -> av * av) (i : nat) (a : av) : option av :=
  match i with
  | O => None
  | S j => if same (fst (w (Z.of_nat j))) a then Some (snd (w (Z.of_nat j))) else find_store w j a
  end.

Fixpoint find_cell (cs : list Z) (i : Z) (k : Z) : option Z :=
  match cs with
  | [] => None
  | c :: r => if c =? k then Some i else find_cell r (i + 1) k
  end.

Definition load (E : env) (y : sym) (a : av) : av :=
  match find_store (yw y) (Z.to_nat (ynw y)) a with
  | Some v => v
  | None =>
    if (avb a =? B_FP) && (0 <=? signed64 (avk a)) && (avk a mod 8 =? 0) then
      let n := avk a / 8 in
      if n =? 0 then AV B_RET 0 0
      else if (n <? 64) && Z.testbit (e_M E) n then AV B_SLOT n 0 else UNK
    else if (avb a =? B_VM) && (avk a =? e_hlim E) then AV B_HLIM 0 0
    else if (avb a =? B_VM) && (avk a =? e_hp E) then AV B_HP 0 0
    else if (avb a =? B_SLOT) && (avk a =? W64 (-3)) && (ava a <? 64) && Z.testbit (e_P E) (ava a) then AV B_HD (ava a) 0
    else if (avb a =? B_SLOT) && (avk a =? 5) && (ava a <? 64) && Z.testbit (e_P E) (ava a) then AV B_TL (ava a) 0
    else if avb a =? B_CONST then
      match find_cell (e_cells E) 0 (avk a) with Some i => AV B_CELL i 0 | None => UNK end
    else UNK
  end.

(** One trip of the loop: the outcome for the instruction [i] decoded at [o]. *)
Inductive iout :=
| INext (o' : Z) (y' : sym)  (* back to the loop head at o' *)
| IFail                      (* x->why set if it was null, returns 0 *)
| IOut.                      (* a form outside the proved slice *)

Definition rb_iter (E : env) (o : Z) (i : ins) (y : sym) : iout :=
  let a := yr y (ir1 i) in let b := yr y (ir2 i) in
  if ik i =? I_LD then INext (o + ilen i) (setr y (ird i) (load E y (add_k a (iimm i))))
  else if ik i =? I_SD then
    if ynw y =? 16 then IFail
    else INext (o + ilen i) (Sym (yr y) (upd (yw y) (ynw y) (add_k a (iimm i), b)) (ynw y + 1))
  else IOut.

(** The loop, from the loop head: [o == stop] returns 1 ([end] = 0), the bounds check fails, or one trip. *)
Inductive rres := RDone (y : sym) | RFail | ROut.

Fixpoint crun (E : env) (code : Z -> Z) (fuel : nat) (o stop : Z) (y : sym) : rres :=
  match fuel with
  | O => RFail
  | S f =>
    if o =? stop then RDone y
    else if (e_len E <? o + 4) || (stop <? o) then RFail
    else
      let i := cdec (code o) (code (o + 1)) (code (o + 2)) (code (o + 3)) in
      match rb_iter E o i y with
      | INext o' y' => crun E code f o' stop y'
      | IFail => RFail
      | IOut => ROut
      end
  end.
