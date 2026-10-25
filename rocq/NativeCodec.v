(* Universal codec correctness for the exact decoded sealed Scheme program.
   The native representation boundary is finite pairs, exact integers and
   byte-spelled symbols. Chez primitive implementation is not assumed proved. *)
From Coq Require Import List String Ascii ZArith Arith Lia.
From Buri Require Import Native NativeComposition NativeSimulation NativeRuntime NativeHelpers SealedInput Encoder Wire.
Import ListNotations.
Module NativeCodec.
Import Native.Native NativeComposition.NativeComposition.
Open Scope string_scope.
Definition P := lookup sealed_native_program.
Ltac start_run := unfold runs; eexists; split; [reflexivity|]; split; [reflexivity|].
Ltac small := unfold executes; exists 10; reflexivity.
Lemma helper_divide : forall n d v,
 NativeHelpers.invoke "non-rational-/" [Integer n;Integer d] = Returned v ->
 runs P "non-rational-/" [Integer n;Integer d] v.
Proof. intros; start_run. exists 30; exact H. Qed.
Lemma helper_floor : forall v w,
 NativeHelpers.invoke "kl:floor" [v] = Returned w -> runs P "kl:floor" [v] w.
Proof. intros; start_run. exists 30; exact H. Qed.
Lemma half : forall rho e n,
 executes P rho e (Integer (Z.of_nat n)) ->
 executes P rho (Call "kl:floor" [Call "non-rational-/" [e;Lit (Integer 2)]])
 (Integer (Z.of_nat (Nat.div2 n))).
Proof.
 intros rho e n E. pose proof (NativeHelpers.natural_halving n) as H.
 destruct (NativeHelpers.invoke "non-rational-/" [Integer (Z.of_nat n);Integer 2]) eqn:D; try discriminate.
 eapply call; [constructor; [|constructor]|eapply helper_floor; exact H].
 eapply call; [constructor; [exact E|constructor; [apply literal|constructor]]|eapply helper_divide; exact D].
Qed.
Lemma helper_equal : forall n m, runs P "kl:=" [Integer n;Integer m] (Boolean (Z.eqb n m)).
Proof. intros; start_run; exists 30; apply NativeHelpers.integer_equality. Qed.
Lemma nat_even : forall n, Z.eqb (Z.of_nat n) (Z.of_nat (Nat.div2 n) * 2) = Nat.eqb n (Nat.div2 n * 2).
Proof.
 intros n. change (Z.eqb (Z.of_nat n) (Z.of_nat (Nat.div2 n) * Z.of_nat 2) = Nat.eqb n (Nat.div2 n * 2)).
 rewrite <- Nat2Z.inj_mul.
 apply Bool.eq_true_iff_eq; rewrite Z.eqb_eq, Nat.eqb_eq; split; [apply Nat2Z.inj|intros; congruence].
Qed.
Lemma nat_prev : forall n, (Z.of_nat (S n) - 1)%Z = Z.of_nat n.
Proof. intros; lia. Qed.
Theorem byte_correct : forall count n,
 runs P "kl:buri.wire-byte" [Integer (Z.of_nat n);Integer (Z.of_nat count)]
 (Text (Wire.bit_text (Encoder.byte_bits n count))).
Proof.
 induction count as [|count IH]; intro n; start_run.
 - exists 10; reflexivity.
 - eapply branch with (flag:=false).
   + change (executes P (arguments ["V5945";"V5946"] [Integer (Z.of_nat n);Integer (Z.of_nat (S count))])
       (Call "eqv?" [Var "V5946";Lit (Integer 0)]) (Boolean false)).
     exists 10. change (Returned (Boolean (Z.eqb (Z.of_nat (S count)) 0)) = Returned (Boolean false)).
     assert (Z.eqb (Z.of_nat (S count)) 0 = false) as Z by (apply Z.eqb_neq; lia). rewrite Z; reflexivity.
   + cbn [body]. eapply binding; [apply half; small|].
     eapply binding with (x:=Text (if Nat.eqb n (Nat.div2 n * 2) then "0" else "1")).
     * eapply branch with (flag:=Nat.eqb n (Nat.div2 n * 2)).
       -- rewrite <- nat_even. eapply call.
          ++ constructor; [small|constructor; [small|constructor]].
          ++ apply helper_equal.
       -- destruct (Nat.eqb n (Nat.div2 n * 2)); apply literal.
     * eapply primitive_call.
       -- constructor; [small|constructor; [|constructor]].
          eapply call with (vs := [Integer (Z.of_nat (Nat.div2 n)); Integer (Z.of_nat count)]).
          ++ constructor; [small|constructor; [|constructor]].
             exists 10. change (Returned (Integer (Z.of_nat (S count)-1)) = Returned (Integer (Z.of_nat count))).
             rewrite nat_prev; reflexivity.
          ++ apply IH.
       -- reflexivity.
       -- cbn [external primitive Encoder.byte_bits Wire.bit_text].
          destruct (Nat.eqb n (Nat.div2 n * 2)); reflexivity.
Qed.
Lemma char_range : forall c,
 Z.geb (Z.of_nat (nat_of_ascii c)) 0 = true /\
 Z.ltb (Z.of_nat (nat_of_ascii c)) 256 = true.
Proof.
 intros c; pose proof (nat_ascii_bounded c); split.
 - apply Z.geb_le; lia.
 - apply Z.ltb_lt; lia.
Qed.
Lemma string_tail : forall c s,
 substring 1 (Z.to_nat (Z.of_nat (String.length (String c s)) - 1)) (String c s) = s.
Proof.
 intros c s. replace (Z.of_nat (String.length (String c s)) - 1)%Z
 with (Z.of_nat (String.length s)) by (cbn [String.length]; lia).
 rewrite Nat2Z.id. cbn [substring]. induction s; cbn; congruence.
Qed.
Theorem string_correct : forall s,
 runs P "kl:buri.wire-string" [Text s] (Text (Wire.bit_text (Wire.string_bits s))).
Proof.
 induction s as [|c s IH]; start_run.
 - exists 10; reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply binding with (x:=Integer (Z.of_nat (nat_of_ascii c))); [small|].
   eapply branch with (flag:=true).
   + eapply conjunction with (flag:=true).
     * exists 10. change (Returned (Boolean (Z.geb (Z.of_nat (nat_of_ascii c)) 0)) = Returned (Boolean true)).
       rewrite (proj1 (char_range c)); reflexivity.
     * exists 10. change (Returned (Boolean (Z.ltb (Z.of_nat (nat_of_ascii c)) 256)) = Returned (Boolean true)).
       rewrite (proj2 (char_range c)); reflexivity.
   + eapply primitive_call.
     * constructor; [apply literal|constructor; [|constructor]].
       eapply binding with (x:=Text (Wire.bit_text (Encoder.byte_bits (nat_of_ascii c) 8))).
       -- eapply call with (vs := [Integer (Z.of_nat (nat_of_ascii c));Integer 8]).
          ++ constructor.
             ** small.
             ** constructor.
              { apply literal. }
              { constructor. }
          ++ exact (byte_correct 8 (nat_of_ascii c)).
       -- eapply primitive_call.
          ++ constructor; [small|constructor; [|constructor]].
             eapply call with (vs:=[Text s]).
             ** constructor; [|constructor].
                eapply binding with (x:=Text (String c s)); [small|].
                eapply primitive_call with (vs:=[Text (String c s);Integer 1;
                   Integer (Z.of_nat (String.length (String c s)))]).
                { constructor; [small|constructor; [apply literal|constructor; [small|constructor]]]. }
                { reflexivity. }
                change ((match (if (Z.leb 0 1 && Z.leb 1 (Z.of_nat (String.length (String c s))) &&
                    Z.leb (Z.of_nat (String.length (String c s))) (Z.of_nat (String.length (String c s))))%bool
                  then Some (Text (substring 1 (Z.to_nat (Z.of_nat (String.length (String c s))-1)) (String c s)))
                  else None) with Some v => Returned v | None => Unsupported end) = Returned (Text s)).
                rewrite Z.leb_refl. assert (Z.leb 1 (Z.of_nat (String.length (String c s))) = true) as B
                  by (apply Z.leb_le; cbn [String.length]; lia).
                rewrite B. cbn [andb Z.leb]. rewrite string_tail; reflexivity.
             ** exact IH.
          ++ reflexivity.
          ++ reflexivity.
     * reflexivity.
     * cbn [external primitive Wire.string_bits Wire.bit_text].
       rewrite Encoder.byte_ascii, Encoder.bit_text_app; reflexivity.
Qed.
Inductive datum := DNil | DInteger (z : Z) | DSymbol (s : string) | DPair (a b : datum).
Fixpoint native d := match d with
 | DNil => Nil | DInteger z => Integer z | DSymbol s => Symbol s
 | DPair a b => Pair (native a) (native b) end.
Fixpoint wire d := match d with
 | DNil => Wire.Nil | DInteger z => Wire.Atom true (spelling z)
 | DSymbol s => Wire.Atom false s | DPair a b => Wire.Cons (wire a) (wire b) end.
Lemma integer_spelling : forall z, runs P "kl:str" [Integer z] (Text (spelling z)).
Proof. intros; start_run; exists 30; apply NativeHelpers.integer_spelling. Qed.
Lemma symbol_spelling : forall s, runs P "kl:str" [Symbol s] (Text s).
Proof. intros; start_run; exists 30; apply NativeHelpers.symbol_spelling. Qed.
Theorem datum_correct : forall d,
 runs P "kl:buri.wire" [native d] (Text (Wire.capture (wire d))).
Proof.
 induction d as [|z|s|a A b B]; start_run.
 - exists 10; reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply call with (vs:=[Text (spelling z)]).
     * constructor; [|constructor]. eapply call; [constructor; [small|constructor]|apply integer_spelling].
     * apply string_correct.
   + reflexivity.
   + reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply call with (vs:=[Text s]).
     * constructor; [|constructor]. eapply call; [constructor; [small|constructor]|apply symbol_spelling].
     * apply string_correct.
   + reflexivity.
   + reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply binding with (x:=Text (Wire.capture (wire a))).
     * eapply call; [constructor; [small|constructor]|exact A].
     * eapply primitive_call.
       -- constructor; [small|constructor; [|constructor]].
          eapply call; [constructor; [small|constructor]|exact B].
       -- reflexivity.
       -- reflexivity.
   + reflexivity.
   + cbn [external primitive wire Wire.capture Wire.encode Wire.bit_text].
     rewrite Encoder.bit_text_app; reflexivity.
Qed.
Theorem evaluator_correct : forall d, exists fuel,
 run fuel sealed_native_program "kl:buri.wire" [native d] = Returned (Text (Wire.capture (wire d))).
Proof. intro d; apply runs_run; apply datum_correct. Qed.
Theorem machine_correct : forall d, exists steps,
 NativeRuntime.invoke steps sealed_native_program "kl:buri.wire" [native d] =
 Returned (Text (Wire.capture (wire d))).
Proof.
 intro d; destruct (evaluator_correct d) as [n H].
 eapply NativeSimulation.run_invoke; exact H.
Qed.
Theorem machine_start_correct : forall d, exists steps,
 NativeRuntime.execute steps P (sealed_start (native d)) = Returned (Text (Wire.capture (wire d))).
Proof.
 intro d; destruct (machine_correct d) as [n H]. exists n; exact H.
Qed.
Theorem concurrent_correct : forall d wa wb out,
 NativeRuntime.concurrent_reaches P (sealed_start (native d),wa)
   ((NativeRuntime.Deliver (Text out),[]),wb) -> out = Wire.capture (wire d).
Proof.
 intros d wa wb out H. destruct (machine_start_correct d) as [n N].
 apply NativeRuntime.execute_trace in N.
 apply NativeRuntime.erase_rebindings in H; cbn in H.
 assert ((NativeRuntime.Deliver (Text out),[]) =
  (NativeRuntime.Deliver (Text (Wire.capture (wire d))),[])) as E by
  (eapply NativeRuntime.terminal_unique; [exact H|exact N|reflexivity|reflexivity]).
 inversion E; reflexivity.
Qed.
Theorem machine_roundtrip : forall d steps out,
 NativeRuntime.execute steps P (sealed_start (native d)) = Returned (Text out) ->
 Wire.decode_text out = Some (wire d).
Proof.
 intros d steps out H. destruct (machine_start_correct d) as [n N].
 apply NativeRuntime.execute_trace in H,N.
 assert ((NativeRuntime.Deliver (Text out),[]) =
  (NativeRuntime.Deliver (Text (Wire.capture (wire d))),[])) as E by
  (eapply NativeRuntime.terminal_unique; [exact H|exact N|reflexivity|reflexivity]).
 inversion E; apply Wire.capture_roundtrip.
Qed.
End NativeCodec.
