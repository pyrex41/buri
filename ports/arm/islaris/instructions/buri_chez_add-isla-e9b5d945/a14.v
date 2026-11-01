From isla Require Import opsem.

Definition a14 : isla_trace :=
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 27%Z)) Mk_annot :t:
  Smt (DefineConst 28%Z (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  Smt (DefineConst 30%Z (Val (Val_Symbolic 29%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 37%Z (Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot; Unop (ZeroExtend 64%N) (Val (Val_Symbolic 30%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 41%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 37%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 54%Z (Manyop Concat [Manyop Concat [Manyop Concat [Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 41%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x3f%Z)) Mk_annot) Mk_annot) Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 41%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 41%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 37%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 41%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot; Unop (SignExtend 64%N) (Val (Val_Symbolic 30%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 55%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 55%Z))]) Mk_annot :t:
  Smt (DefineConst 56%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 56%Z))]) Mk_annot :t:
  Smt (DefineConst 57%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 57%Z))]) Mk_annot :t:
  Smt (DefineConst 58%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 58%Z))]) Mk_annot :t:
  Smt (DefineConst 59%Z (Val (Val_Symbolic 41%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R23" [] (RegVal_Base (Val_Symbolic 59%Z)) Mk_annot :t:
  Smt (DeclareConst 60%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 60%Z)) Mk_annot :t:
  Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 60%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
  tnil
.
