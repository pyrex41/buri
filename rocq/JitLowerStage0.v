(* Shen/JIT Phase 2: translation validation of stage 0 output. For each definition, the form as read
   (<file>.forms) and its code object (<file>.sbc) are decoded here from generic trees, and
   JitLowerCheck decides whether the code is related to the definition. The trees come from a
   trusted tokenizer (tests/shen-jit/stage0_to_rocq.py, OB-JIT-LOWER-READER). *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii.
From Buri Require Import Observation KLSyntax KLValue KLSemantics JitBytecode JitLowerRel JitLowerCheck.
Import ListNotations.
Module JitLowerStage0.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel JitLowerCheck.JitLowerCheck.
Module B := JitBytecode.JitBytecode.

Inductive sx := XSym (s : string) | XInt (z : Z) | XReal (b : N) | XStr (t : list N) | XList (l : list sx).

Fixpoint to_value (x : sx) : value := match x with
 | XSym s => if String.eqb s "true" then VBool true else if String.eqb s "false" then VBool false
             else VSym (of_string s)
 | XInt z => VNum (NInt z) | XReal b => VNum (NFloat b) | XStr t => VStr t
 | XList l => fold_right (fun a d => VCons (to_value a) d) VNil l end.
Fixpoint to_val (x : sx) : B.val := match x with
 | XSym s => if String.eqb s "true" then B.VBool true else if String.eqb s "false" then B.VBool false
             else B.VSym (B.sym s)
 | XInt z => B.VFix z | XReal b => B.VReal b | XStr t => B.VStr t
 | XList l => fold_right (fun a d => B.VPair (to_val a) d) B.VNil l end.

Inductive verdict := Accepted (f : name) | Rejected (f : name) | Unparsed.

Definition judge (form sbc : sx) : verdict :=
 match parse [] (to_value form), to_val sbc with
 | Some (EDefun f ps b), B.VPair (B.VSym _) (B.VPair (B.VSym g) (B.VPair code B.VNil)) =>
   if negb (Pos.eqb (B.sym_of_text f) g) then Unparsed else
   match B.build_code B.prim_tree 64 code with
   | B.LOk c =>
     if (N.eqb (B.code_arity c) (N.of_nat (List.length ps))
         && match B.code_entry c with None => true | Some _ => false end
         && check_fn c ps b)%bool
     then Accepted f else Rejected f
   | B.LErr _ => Rejected f end
 | _, _ => Unparsed end.

Fixpoint judge_all (fs ss : list sx) : list verdict := match fs, ss with
 | f :: fs, s :: ss => judge f s :: judge_all fs ss
 | [], [] => []
 | _, _ => [Unparsed] end.

Definition tally (fs ss : list sx) : nat * nat * nat * list name :=
 fold_right (fun v acc => let '(a, r, u, names) := acc in match v with
   | Accepted f => (S a, r, u, f :: names)
   | Rejected _ => (a, S r, u, names)
   | Unparsed => (a, r, S u, names) end) (0, 0, 0, [])%nat (judge_all fs ss).
End JitLowerStage0.
