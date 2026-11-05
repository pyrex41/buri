Require Import isla.isla_lang.
Require Export isla.instructions.buri_chez_add.a0.
Require Export isla.instructions.buri_chez_add.a4.
Require Export isla.instructions.buri_chez_add.a8.
Require Export isla.instructions.buri_chez_add.ac.
Require Export isla.instructions.buri_chez_add.a10.
Require Export isla.instructions.buri_chez_add.a14.
Require Export isla.instructions.buri_chez_add.a18.
Require Export isla.instructions.buri_chez_add.a1c.
Require Export isla.instructions.buri_chez_add.a20.

Definition instr_map := [
  (0x0%Z, a0 (* cmp x23, #0x2 *));
  (0x4%Z, a4 (* b.ne 84 *));
  (0x8%Z, a8 (* orr x30, x0, x1 *));
  (0xc%Z, ac (* tst x30, #0x7 *));
  (0x10%Z, a10 (* b.ne 24 *));
  (0x14%Z, a14 (* adds x23, x0, x1 *));
  (0x18%Z, a18 (* b.vs 24 *));
  (0x1c%Z, a1c (* ldur x10, [x20] *));
  (0x20%Z, a20 (* br x10 *))
].
