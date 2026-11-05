(* Decode probe: prints what each word of program.S decodes to, using chain's
   guard elimination. Not evidence; the theorems are in BuriJitWords.v. *)
Require Import SailStdpp.Base SailStdpp.Real SailStdpp.ConcurrencyInterfaceTypes
  SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import armv9_types arm_extras armv9.
Require Import BuriArm.BuriArmDecode.
Import Defs.
Open Scope Z.

Ltac pchain :=
  lazymatch goal with
  | |- (and_boolM (returnM ?b) ?X >>= fun w => if w then ?T else ?E) = _ =>
      let v := eval vm_compute in b in
      lazymatch v with
      | false => refine (guard_skip b X T E _ ltac:(vmdec) _); pchain
      | true => idtac "TAKEN:"; idtac T; refine (guard_take b _ T E _ _ ltac:(vmdec) _ _); [pchain | reflexivity]
      end
  | |- (if ?b then ?T else ?E) = _ =>
      let v := eval vm_compute in b in
      lazymatch v with
      | false => refine (if_skip b T E _ ltac:(vmdec) _); pchain
      | true => refine (if_take b T E _ ltac:(vmdec) _); pchain
      end
  | |- __DecodeA64 _ _ = _ => unfold __DecodeA64; pchain
  | |- __DecodeA64_LoadStore _ _ = _ => unfold __DecodeA64_LoadStore; pchain
  | |- __DecodeA64_BranchExcSys _ _ = _ => unfold __DecodeA64_BranchExcSys; pchain
  | |- __DecodeA64_DataProcImm _ _ = _ => unfold __DecodeA64_DataProcImm; pchain
  | |- __DecodeA64_DataProcReg _ _ = _ => unfold __DecodeA64_DataProcReg; pchain
  | |- ?l = _ => idtac "ELSE:"; idtac l; reflexivity
  end.

Set Printing Width 200.
Ltac probe w := let pc := fresh in intro pc; eexists; unfold w; pchain.
Definition w_mov : mword 32 := Ox"52800540".   Goal forall pc, exists m, __DecodeA64 pc w_mov = m. idtac "mov w0,#42". Time probe w_mov. Qed.
Definition w_ret : mword 32 := Ox"D65F03C0".   Goal forall pc, exists m, __DecodeA64 pc w_ret = m. idtac "ret". Time probe w_ret. Qed.
Definition w_str : mword 32 := Ox"B90000A4".   Goal forall pc, exists m, __DecodeA64 pc w_str = m. idtac "str w4,[x5]". Time probe w_str. Qed.
Definition w_blr : mword 32 := Ox"D63F00A0".   Goal forall pc, exists m, __DecodeA64 pc w_blr = m. idtac "blr x5". Time probe w_blr. Qed.
Definition w_isb : mword 32 := Ox"D5033FDF".   Goal forall pc, exists m, __DecodeA64 pc w_isb = m. idtac "isb". Time probe w_isb. Qed.
Definition w_dsb : mword 32 := Ox"D5033B9F".   Goal forall pc, exists m, __DecodeA64 pc w_dsb = m. idtac "dsb ish". Time probe w_dsb. Qed.
Definition w_ic  : mword 32 := Ox"D50B7525".   Goal forall pc, exists m, __DecodeA64 pc w_ic = m. idtac "ic ivau,x5". Time probe w_ic. Qed.
Definition w_dc  : mword 32 := Ox"D50B7B25".   Goal forall pc, exists m, __DecodeA64 pc w_dc = m. idtac "dc cvau,x5". Time probe w_dc. Qed.
