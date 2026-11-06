(** * The template of one [(move D S)], as a list of 16-bit halves.

    This is the trusted statement of what the emitter must produce for this opcode, written
    from docs/design.md and src/runtime/jit.c.  [MoveDecode.v] checks these encodings against
    the model's own decoder, so they are not just a copy of the checker's formulas.
    Forms outside the domain, which are slot offsets above 2047 and constant sources, have
    no template here. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.

Definition c_mv (rd rs : Z) : Z := 32770 + rd * 128 + rs * 4.
Definition c_off (off : Z) : Z := ((off / 8) mod 8) * 1024 + ((off / 64) mod 4) * 32 + 8.
Definition c_ld_a0 (off : Z) : Z := 24576 + c_off off.
Definition c_sd_a0 (off : Z) : Z := 57344 + c_off off.
Definition ld_s0 (rd off : Z) : Z := off * 2^20 + 8 * 2^15 + 3 * 2^12 + rd * 128 + 3.
Definition sd_a0 (off : Z) : Z :=
  (off / 32) * 2^25 + 10 * 2^20 + 8 * 2^15 + 3 * 2^12 + (off mod 32) * 128 + 35.
Definition split32 (x : Z) : list Z := [x mod 65536; x / 65536].

Definition is_home (homes n : Z) : bool := (2 <=? n) && (n <? homes + 2).

Definition src_template (homes cached src : Z) : list Z :=
  if src =? cached then [c_mv 10 18]
  else if is_home homes src then [c_mv 10 (18 + src)]
  else if 8 * src <=? 248 then [c_ld_a0 (8 * src)]
  else split32 (ld_s0 10 (8 * src)).

Definition store_template (dst : Z) : list Z :=
  if 8 * dst <=? 248 then [c_sd_a0 (8 * dst)] else split32 (sd_a0 (8 * dst)).

Definition move_template (homes cached dst src keep : Z) (store : bool) : list Z :=
  if is_home homes dst then
    if is_home homes src then
      if src =? dst then [] else [c_mv (18 + dst) (18 + src)]
    else split32 (ld_s0 (18 + dst) (8 * src))
  else
    src_template homes cached src ++ (if store then store_template dst else []) ++
    (if keep =? 1 then [c_mv 18 10] else []).

(** The checker's domain. *)
Definition in_domain (homes cached dst src keep : Z) : Prop :=
  0 <= dst <= 255 /\ 0 <= src <= 255 /\ 0 <= homes <= 6 /\ (keep = 0 \/ keep = 1) /\
  (homes <> 0 -> cached = 4294967295).
