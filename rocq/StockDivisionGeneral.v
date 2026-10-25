(* Source-linked wrapper contract for all values and all signed exact
   denominators. Chez division/classification/rounding remain named contracts. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native ObserverEffects StockDivision CheckedFileIO.
Import ListNotations.
Module StockDivisionGeneral.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Definition operation (divide:value->value->result) (is_integer:value->bool) (round:value->result) name args : computation :=
 return_result (match name,args with
 | "/",[x;y]=>divide x y
 | "integer?",[v]=>Returned (Boolean (is_integer v))
 | "inexact",[v]=>round v
 | _,_=>external name args end).
Definition P := lookup StockDivision.program.
Definition rho x y := arguments ["x";"y"] [x;y].
Definition invoke divide classify round x y := match P "non-rational-/" with
 | Some d=>eval_with 5 P (operation divide classify round) (arguments (params d) [x;y]) (body d) Nil
 | None=>Out Unsupported Nil [] end.
Definition expected (divide:value->value->result) (classify:value->bool) (round:value->result) (x y:value) := match divide x y with
 | Returned v=>if classify v then Returned v else round v | r=>r end.
Lemma divide_stage : forall divide classify round x y,
 eval_with 4 P (operation divide classify round) (rho x y) (Call "/" [Var "x";Var "y"]) Nil =
 Out (divide x y) Nil [].
Proof. reflexivity. Qed.
Lemma continuation : forall divide classify round x y v,
 eval_with 4 P (operation divide classify round) (Native.bind (rho x y) "result" v)
 (If (Call "integer?" [Var "result"]) (Var "result") (Call "inexact" [Var "result"])) Nil =
 Out (if classify v then Returned v else round v) Nil [].
Proof.
 intros; rewrite CheckedFileIO.if_step.
 assert (eval_with 3 P (operation divide classify round) (Native.bind (rho x y) "result" v)
 (Call "integer?" [Var "result"]) Nil=Out (Returned (Boolean (classify v))) Nil []) as G by reflexivity.
 rewrite G; cbn [answer records trace]; destruct (classify v); reflexivity.
Qed.
Theorem all_value_wrapper_contract : forall divide classify round x y,
 invoke divide classify round x y=Out (expected divide classify round x y) Nil [].
Proof.
 intros.
 match goal with |- _ = ?rhs => change (eval_with 5 P (operation divide classify round) (rho x y)
 (Let "result" (Call "/" [Var "x";Var "y"])
 (If (Call "integer?" [Var "result"]) (Var "result") (Call "inexact" [Var "result"]))) Nil=rhs) end.
 rewrite CheckedFileIO.let_step,divide_stage.
 unfold expected. destruct (divide x y) eqn:D; cbn [answer records trace];
 try reflexivity; rewrite continuation; reflexivity.
Qed.
Theorem division_failure_is_not_rounded : forall divide classify round x y failure,
 divide x y=failure -> failed failure -> invoke divide classify round x y=Out failure Nil [].
Proof.
 intros; rewrite all_value_wrapper_contract; unfold expected; rewrite H.
 destruct failure; try contradiction; reflexivity.
Qed.
Definition signed_ratio n d := match d with
 | Zpos p=>ratio n (Zpos p) | Zneg p=>ratio (-n) (Zpos p) | Z0=>None end.
Definition exact_divide zero_failure x y := match x,y with
 | Integer n,Integer d=>match signed_ratio n d with Some v=>Returned v|None=>zero_failure end
 | _,_=>Unsupported end.
Theorem positive_profile_preserved : forall n p, signed_ratio n (Zpos p)=ratio n (Zpos p).
Proof. reflexivity. Qed.
Theorem negative_denominator_normalized : forall n p, signed_ratio n (Zneg p)=ratio (-n) (Zpos p).
Proof. reflexivity. Qed.
Theorem signed_exact_wrapper : forall zero_failure round n d,
 failed zero_failure ->
 invoke (exact_divide zero_failure) integral round (Integer n) (Integer d) =
 Out (match signed_ratio n d with
 | Some v=>if integral v then Returned v else round v | None=>zero_failure end) Nil [].
Proof.
 intros zero_failure round n d F; rewrite all_value_wrapper_contract; unfold expected,exact_divide.
 destruct (signed_ratio n d); [reflexivity|].
 destruct zero_failure; try contradiction; reflexivity.
Qed.
End StockDivisionGeneral.
