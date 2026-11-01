From isla Require Import opsem.

Definition a8 : isla_trace :=
  Smt (DeclareConst 31%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 31%Z)) Mk_annot :t:
  Smt (DeclareConst 33%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 33%Z)) Mk_annot :t:
  Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Symbolic 31%Z) Mk_annot; Val (Val_Symbolic 33%Z) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R30" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
  Smt (DeclareConst 40%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
  Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 40%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
  tnil
.
