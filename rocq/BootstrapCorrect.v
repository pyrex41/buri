(* Actual boolean-aware bootstrap tagging bodies, not a protocol-only proof. *)
From Coq Require Import List String Ascii ZArith Arith Lia.
From Buri Require Import Wire EncoderFrontend CaptureTag Native NativeValidation NativeHelpers NativeComposition NativeSimulation NativeRuntime NativeCodec AdapterCorrect BootstrapInput.
Import ListNotations.
Module BootstrapCorrect.
Import Native.Native NativeComposition.NativeComposition.
Module F := EncoderFrontend.EncoderFrontend.
Module C := NativeCodec.NativeCodec.
Module A := AdapterCorrect.AdapterCorrect.
Open Scope string_scope.
Definition program := (bootstrap_program ++ NativeHelpers.helpers)%list.
Definition P := lookup program.
Definition byte_data := A.byte_data.
Definition tag1 := A.tag1.
Inductive node := BNil | BSymbol (s:string) | BNumber (n:nat) | BText (s:string)
 | BBoolean (b:bool) | BPair (a b:node).
Fixpoint lift d := match d with
 | BNil => Nil | BSymbol s => Symbol s | BNumber n => Integer (Z.of_nat n)
 | BText s => Text s | BBoolean b => Boolean b | BPair a b => Pair (lift a) (lift b) end.
Fixpoint tag_data d := match d with
 | BNil => C.DPair (C.DSymbol "nil") C.DNil
 | BSymbol s => tag1 "sym" (C.DSymbol s)
 | BNumber n => tag1 "num" (C.DInteger (Z.of_nat n))
 | BText s => tag1 "text" (byte_data s)
 | BBoolean b => tag1 "bool" (C.DInteger (if b then 1 else 0))
 | BPair a b => C.DPair (C.DSymbol "pair") (C.DPair (tag_data a) (C.DPair (tag_data b) C.DNil)) end.
Ltac start_run := unfold runs; eexists; split; [reflexivity|]; split; [reflexivity|].
Ltac small := unfold executes; exists 10; reflexivity.
Theorem bytes_correct : forall s,
 runs P "kl:buri.native-bytes" [Text s] (C.native (byte_data s)).
Proof.
 induction s as [|c s IH]; start_run.
 - exists 10; reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply binding with (x:=Integer (Z.of_nat (nat_of_ascii c))); [small|].
   eapply primitive_call.
   + constructor; [small|constructor; [|constructor]].
     eapply call with (vs:=[Text s]).
     * constructor; [|constructor].
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
       rewrite B; cbn [andb Z.leb]. rewrite C.string_tail; reflexivity.
     * exact IH.
   + reflexivity.
   + reflexivity.
Qed.
Theorem node_correct : forall d,
 runs P "kl:buri.native-node" [lift d] (C.native (tag_data d)).
Proof.
 induction d as [|s|n|s|b|a A b B]; start_run.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|]. small.
 - do 6 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|]. small.
 - do 5 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|]. small.
 - do 4 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply call; [constructor; [small|constructor]|apply bytes_correct].
   + reflexivity.
   + reflexivity.
 - destruct b.
   + eapply branch with (flag:=true); [small|]. small.
   + eapply branch with (flag:=false); [small|].
     eapply branch with (flag:=true); [small|]. small.
 - do 3 (eapply branch with (flag:=false); [small|]).
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply binding with (x:=C.native (tag_data a)).
     * eapply call; [constructor; [small|constructor]|exact A].
     * eapply primitive_call.
       -- constructor; [small|constructor; [|constructor]].
          eapply call; [constructor; [small|constructor]|exact B].
       -- reflexivity.
       -- reflexivity.
   + reflexivity.
   + reflexivity.
Qed.
Fixpoint admitted d : Prop := match d with
 | BNumber n => n <= 256 | BPair a b => admitted a /\ admitted b | _ => True end.
Fixpoint depth d := match d with BPair a b => S (Nat.max (depth a) (depth b)) | _ => 1 end.
Lemma integer_roundtrip : forall n, n <= 256 -> NativeValidation.integer (spelling (Z.of_nat n)) = Some (Z.of_nat n).
Proof. intros n H; do 257 (destruct n; [vm_compute; reflexivity|]); lia. Qed.
Theorem tag_roundtrip : forall d fuel, admitted d -> depth d <= fuel ->
 untag fuel (C.wire (tag_data d)) = Some (lift d).
Proof.
 induction d; intros [|fuel] A D; cbn [depth] in D; try lia;
 cbn [tag_data tag1 A.tag1 C.wire untag lift]; try reflexivity.
 - rewrite integer_roundtrip by exact A; reflexivity.
 - rewrite A.bytes_wire, CaptureTag.bytes_roundtrip; reflexivity.
 - destruct b; reflexivity.
 - destruct A as [A B]. rewrite IHd1,IHd2; auto; lia.
Qed.
Theorem machine_correct : forall d, exists steps,
 NativeRuntime.invoke steps program "kl:buri.native-node" [lift d] = Returned (C.native (tag_data d)).
Proof.
 intro d; destruct (runs_run _ _ _ _ (node_correct d)) as [n H].
 eapply NativeSimulation.run_invoke; exact H.
Qed.
Theorem wire_roundtrip : forall d, admitted d -> exists tag_steps wire_steps,
 NativeRuntime.invoke tag_steps program "kl:buri.native-node" [lift d] = Returned (C.native (tag_data d)) /\
 NativeRuntime.invoke wire_steps SealedInput.sealed_native_program "kl:buri.wire" [C.native (tag_data d)] =
 Returned (Text (Wire.capture (C.wire (tag_data d)))) /\
 (match Wire.decode_text (Wire.capture (C.wire (tag_data d))) with
 | Some raw => untag (depth d) raw | None => None end) = Some (lift d).
Proof.
 intros d H; destruct (machine_correct d) as [n N]; destruct (C.machine_correct (tag_data d)) as [m M].
 exists n,m; split; [exact N|]. split; [exact M|].
 rewrite Wire.capture_roundtrip; apply tag_roundtrip; auto.
Qed.
Theorem booleans_not_symbols : forall b s, lift (BBoolean b) <> lift (BSymbol s).
Proof. discriminate. Qed.
End BootstrapCorrect.
