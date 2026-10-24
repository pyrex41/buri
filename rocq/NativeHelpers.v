From Coq Require Import List String ZArith Bool Lia.
From Buri Require Import Native NativeRuntime Sealed EncoderFrontend.
Import ListNotations.
Open Scope string_scope.
Module NativeHelpers.
Import Native.Native.
Fixpoint lift (v : EncoderFrontend.EncoderFrontend.node) : value := match v with
 | EncoderFrontend.Nil => Nil | EncoderFrontend.Sym s => Symbol s
 | EncoderFrontend.TextNode s => Text s | EncoderFrontend.Num n => Integer (Z.of_nat n)
 | EncoderFrontend.Pair a b => Pair (lift a) (lift b) end.
Definition helper_definition v := match elements v with
 | Some [Symbol name;lambda] => match elements lambda with
   | Some [Symbol "lambda";args;b] => match elements args,decode 100 b with
     | Some ps,Some e => match names ps with Some ps => Some (name,Def ps e) | _ => None end
     | _,_ => None end
   | _ => None end | _ => None end.
Fixpoint helper_definitions xs := match xs with
 | [] => Some []
 | x::xs => match helper_definition x,helper_definitions xs with
   | Some d,Some ds => Some (d::ds) | _,_ => None end end.
Definition helpers := Eval vm_compute in match elements (lift SealedCapture.helper_template) with
 | Some xs => match helper_definitions xs with Some ds => ds | _ => [] end | _ => [] end.
Theorem helpers_exact :
 match elements (lift SealedCapture.helper_template) with
 | Some xs => helper_definitions xs | _ => None end = Some helpers.
Proof. vm_compute. reflexivity. Qed.
Definition invoke name args := run 30 helpers name args.
Theorem boolean_identity : forall b,
 invoke "kl:_scm.assert-boolean" [Boolean b] = Returned (Boolean b).
Proof. intros []; reflexivity. Qed.
Theorem boolean_type_error : forall v,
 (match v with Boolean _ => false | _ => true end) = true ->
 invoke "kl:_scm.assert-boolean" [v] = Raised (Symbol "sealed-encoder") (Text "Expected boolean").
Proof. destruct v; intro H; try discriminate; reflexivity. Qed.
Theorem exact_integer_classification : forall z,
 invoke "kl:buri.exact-integer?" [Integer z] = Returned (Boolean true).
Proof. reflexivity. Qed.
Theorem inexact_classification : forall z,
 invoke "kl:buri.exact-integer?" [Inexact z] = Returned (Boolean false).
Proof. reflexivity. Qed.
Theorem fraction_classification : forall n d,
 invoke "kl:buri.exact-integer?" [Fraction n d] = Returned (Boolean (Z.eqb (Z.rem n (Z.pos d)) 0)).
Proof. intros n d. change
 ((if Z.eqb (Z.rem n (Z.pos d)) 0 then Returned (Boolean true) else Returned (Boolean false)) =
 Returned (Boolean (Z.eqb (Z.rem n (Z.pos d)) 0))).
 destruct (Z.eqb (Z.rem n (Z.pos d)) 0); reflexivity. Qed.
Theorem symbol_classification : forall v,
 invoke "kl:symbol?" [v] = Returned (Boolean (match v with Symbol _ => true | _ => false end)).
Proof. destruct v; reflexivity. Qed.
Theorem integer_spelling : forall z,
 invoke "kl:str" [Integer z] = Returned (Text (spelling z)).
Proof. reflexivity. Qed.
Theorem symbol_spelling : forall s,
 invoke "kl:str" [Symbol s] = Returned (Text s).
Proof. reflexivity. Qed.
Theorem exact_division : forall n d,
 invoke "non-rational-/" [Integer n;Integer d] =
 match ratio n d with Some v => Returned v | _ => Unsupported end.
Proof. reflexivity. Qed.
Theorem exact_floor : forall n,
 invoke "kl:floor" [Integer n] = Returned (Integer n).
Proof. reflexivity. Qed.
Theorem fractional_floor : forall n d,
 invoke "kl:floor" [Fraction n d] = Returned (Integer (Z.div n (Z.pos d))).
Proof. reflexivity. Qed.
Theorem exact_halving : forall n, (0 <= n)%Z ->
 (match invoke "non-rational-/" [Integer n;Integer 2] with
  | Returned v => invoke "kl:floor" [v] | r => r end) =
 Returned (Integer (Z.div n 2)).
Proof.
 intros n N. rewrite exact_division. unfold ratio.
 destruct (Z.eqb (Z.rem n 2) 0).
 - rewrite exact_floor, Z.quot_div_nonneg; auto; lia.
 - apply fractional_floor.
Qed.
Theorem natural_halving : forall n,
 (match invoke "non-rational-/" [Integer (Z.of_nat n);Integer 2] with
  | Returned v => invoke "kl:floor" [v] | r => r end) =
 Returned (Integer (Z.of_nat (Nat.div2 n))).
Proof.
 intros n. rewrite exact_halving by lia.
 rewrite Nat.div2_div, Nat2Z.inj_div. reflexivity.
Qed.
Theorem integer_equality : forall n m,
 invoke "kl:=" [Integer n;Integer m] = Returned (Boolean (Z.eqb n m)).
Proof. reflexivity. Qed.
Definition machine_invoke name args := NativeRuntime.invoke 20 helpers name args.
Theorem machine_boolean_identity : forall b,
 machine_invoke "kl:_scm.assert-boolean" [Boolean b] = Returned (Boolean b).
Proof. intros []; reflexivity. Qed.
Theorem machine_boolean_error : forall v,
 (match v with Boolean _ => false | _ => true end) = true ->
 machine_invoke "kl:_scm.assert-boolean" [v] = Raised (Symbol "sealed-encoder") (Text "Expected boolean").
Proof. destruct v; intro H; try discriminate; reflexivity. Qed.
Theorem machine_integer_classification : forall z,
 machine_invoke "kl:buri.exact-integer?" [Integer z] = Returned (Boolean true).
Proof. reflexivity. Qed.
Theorem machine_inexact_classification : forall z,
 machine_invoke "kl:buri.exact-integer?" [Inexact z] = Returned (Boolean false).
Proof. reflexivity. Qed.
Theorem machine_symbol_classification : forall v,
 machine_invoke "kl:symbol?" [v] = Returned (Boolean (match v with Symbol _ => true | _ => false end)).
Proof. destruct v; reflexivity. Qed.
Theorem machine_integer_spelling : forall z,
 machine_invoke "kl:str" [Integer z] = Returned (Text (spelling z)).
Proof. reflexivity. Qed.
Theorem machine_symbol_spelling : forall s,
 machine_invoke "kl:str" [Symbol s] = Returned (Text s).
Proof. reflexivity. Qed.
Theorem machine_integer_equality : forall n m,
 machine_invoke "kl:=" [Integer n;Integer m] = Returned (Boolean (Z.eqb n m)).
Proof. reflexivity. Qed.
Theorem machine_floor : forall z,
 machine_invoke "kl:floor" [Integer z] = Returned (Integer z).
Proof. reflexivity. Qed.
Theorem machine_fractional_floor : forall n d,
 machine_invoke "kl:floor" [Fraction n d] = Returned (Integer (Z.div n (Z.pos d))).
Proof. reflexivity. Qed.
Theorem machine_division : forall n d,
 machine_invoke "non-rational-/" [Integer n;Integer d] =
 match ratio n d with Some v => Returned v | _ => Unsupported end.
Proof.
 intros n d. change
 (NativeRuntime.execute 15 (lookup helpers)
  (match (match ratio n d with Some v => Returned v | None => Unsupported end) with
   | Returned v => (NativeRuntime.Deliver v,[])
   | r => (NativeRuntime.Fault r,[]) end) =
  match ratio n d with Some v => Returned v | None => Unsupported end).
 destruct (ratio n d); reflexivity.
Qed.
Theorem helper_execution_ignores_rebinding : forall name args v start w w' observed,
 machine_invoke name args = Returned v ->
 lookup helpers name = Some start ->
 NativeRuntime.concurrent_reaches (lookup helpers)
  ((NativeRuntime.Enter (arguments (params start) args) (body start),[]),w)
  ((NativeRuntime.Deliver observed,[]),w') -> observed = v.
Proof.
 intros name args v start w w' observed R D C.
 unfold machine_invoke, NativeRuntime.invoke in R. rewrite D in R.
 destruct (Nat.eqb (List.length (params start)) (List.length args)); try discriminate.
 apply NativeRuntime.execute_trace in R.
 apply NativeRuntime.erase_rebindings in C; cbn in C.
 assert ((NativeRuntime.Deliver observed,[]) = (NativeRuntime.Deliver v,[])) as E by
  (eapply NativeRuntime.terminal_unique; eauto; reflexivity).
 inversion E; reflexivity.
Qed.
End NativeHelpers.
