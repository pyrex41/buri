(* Actual upstream wrapper, independently read from its exact Scheme source.
   Rounding is an external contract, deliberately not idealized as exact. *)
From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeHelpers SourceReader StockDivisionInput ObserverEffects CheckedFileIO.
Import ListNotations.
Module StockDivision.
Import Native.Native ObserverEffects.ObserverEffects.
Open Scope string_scope.
Definition source_nodes := option_map (map NativeHelpers.lift) (SourceReader.read stock_division_source).
Definition decoded := match source_nodes with Some xs=>definitions 20 xs|None=>None end.
Definition program := Eval vm_compute in match decoded with Some ds=>ds|None=>[] end.
Theorem source_decoded : decoded = Some program /\ map fst program = ["non-rational-/"].
Proof. vm_compute; split; reflexivity. Qed.
Lemma wrapper_shape : lookup program "non-rational-/" = Some (Def ["x";"y"]
 (Let "result" (Call "/" [Var "x";Var "y"])
 (If (Call "integer?" [Var "result"]) (Var "result") (Call "inexact" [Var "result"])))).
Proof. reflexivity. Qed.
Definition operation (round:value->result) name args : computation := fun st=>
 Out (match name,args with "inexact",[v]=>round v|_,_=>external name args end) st [].
Definition invoke round x y := match lookup program "non-rational-/" with
 | Some d=>eval_with 5 (lookup program) (operation round) (arguments (params d) [Integer x;Integer y]) (body d) Nil
 | None=>Out Unsupported Nil [] end.
Definition rho n d := arguments ["x";"y"] [Integer n;Integer d].
Lemma division_step : forall round n d,
 eval_with 4 (lookup program) (operation round) (rho n d)
 (Call "/" [Var "x";Var "y"]) Nil =
 Out (match ratio n d with Some v=>Returned v|None=>Unsupported end) Nil [].
Proof. reflexivity. Qed.
Lemma continuation : forall round n d v,
 eval_with 4 (lookup program) (operation round) (Native.bind (rho n d) "result" v)
 (If (Call "integer?" [Var "result"]) (Var "result") (Call "inexact" [Var "result"])) Nil =
 Out (if integral v then Returned v else round v) Nil [].
Proof.
 intros round n d v.
 rewrite CheckedFileIO.if_step.
 assert (eval_with 3 (lookup program) (operation round) (Native.bind (rho n d) "result" v)
 (Call "integer?" [Var "result"]) Nil = Out (Returned (Boolean (integral v))) Nil []) as G by reflexivity.
 rewrite G. cbn [answer records trace].
 destruct (integral v); reflexivity.
Qed.
Theorem wrapper_contract : forall round n d,
 invoke round n d = Out
 (match ratio n d with
 | Some v=>if integral v then Returned v else round v
 | None=>Unsupported end) Nil [].
Proof.
 intros round n d.
 match goal with |- _ = ?rhs => change (eval_with 5 (lookup program) (operation round) (rho n d)
 (Let "result" (Call "/" [Var "x";Var "y"])
 (If (Call "integer?" [Var "result"]) (Var "result") (Call "inexact" [Var "result"]))) Nil = rhs) end.
 rewrite CheckedFileIO.let_step, division_step.
 destruct (ratio n d); cbn [answer records trace]; [rewrite continuation|]; reflexivity.
Qed.
Theorem integral_quotient_is_exact : forall round n d q,
 ratio n d = Some (Integer q) -> invoke round n d = Out (Returned (Integer q)) Nil [].
Proof. intros; rewrite wrapper_contract,H; reflexivity. Qed.
Theorem fractional_quotient_delegates : forall round n d a b,
 ratio n d = Some (Fraction a b) -> Z.rem a (Z.pos b) <> 0%Z ->
 invoke round n d = Out (round (Fraction a b)) Nil [].
Proof.
 intros; rewrite wrapper_contract,H; cbn [integral].
 assert (Z.eqb (Z.rem a (Z.pos b)) 0 = false) as E by (apply Z.eqb_neq; assumption).
 rewrite E; reflexivity.
Qed.
Theorem precision_loss_permitted_by_wrapper : forall round,
 invoke round 9007199254740995 2 = Out (round (Fraction 9007199254740995 2)) Nil [].
Proof. intro; rewrite wrapper_contract; reflexivity. Qed.
Theorem rounding_failure_propagates : forall round n d a b failure,
 ratio n d = Some (Fraction a b) -> Z.rem a (Z.pos b) <> 0%Z ->
 round (Fraction a b) = failure -> invoke round n d = Out failure Nil [].
Proof. intros; rewrite fractional_quotient_delegates with (a:=a) (b:=b) by assumption; now rewrite H1. Qed.
Theorem replacement_floor_division : forall n d,
 (match NativeHelpers.invoke "non-rational-/" [Integer n;Integer (Z.pos d)] with
 | Returned v=>NativeHelpers.invoke "kl:floor" [v]|r=>r end) =
 Returned (Integer (Z.div n (Z.pos d))).
Proof.
 intros n d; rewrite NativeHelpers.exact_division; unfold ratio.
 destruct (Z.eqb (Z.rem n (Z.pos d)) 0) eqn:E.
 - rewrite NativeHelpers.exact_floor.
   apply Z.eqb_eq in E. rewrite Z.quot_div_exact; [reflexivity|lia|].
   assert (Z.pos d <> 0%Z) as D by lia.
   apply (proj1 (Z.rem_divide n (Z.pos d) D)); exact E.
 - apply NativeHelpers.fractional_floor.
Qed.
Theorem replacement_signed_halving : forall n,
 (match NativeHelpers.invoke "non-rational-/" [Integer n;Integer 2] with
 | Returned v=>NativeHelpers.invoke "kl:floor" [v]|r=>r end) = Returned (Integer (Z.div n 2)).
Proof. intro; apply (replacement_floor_division n 2%positive). Qed.
Theorem unsupported_denominator_profile : forall round n d,
 (d <= 0)%Z -> invoke round n d = Out Unsupported Nil [].
Proof. intros round n d H; rewrite wrapper_contract; destruct d; try reflexivity; lia. Qed.
End StockDivision.
