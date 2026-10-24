(* Correspondence for the captured Shen tagging functions, under a fixed
   private table containing their exact generated bodies and pinned helpers.
   The effectful metadata/IO exporter is deliberately excluded. *)
From Coq Require Import List String Ascii ZArith Arith Lia.
From Buri Require Import Wire EncoderFrontend CaptureTag Native NativeHelpers NativeComposition NativeSimulation NativeRuntime NativeCodec AdapterInput.
Import ListNotations.
Module AdapterCorrect.
Import Native.Native NativeComposition.NativeComposition.
Module F := EncoderFrontend.EncoderFrontend.
Module C := NativeCodec.NativeCodec.
Open Scope string_scope.
Definition program := (firstn 2 adapter_program ++ NativeHelpers.helpers)%list.
Definition P := lookup program.
Fixpoint byte_data s := match s with
 | EmptyString => C.DNil
 | String c s => C.DPair (C.DInteger (Z.of_nat (nat_of_ascii c))) (byte_data s) end.
Definition tag1 name d := C.DPair (C.DSymbol name) (C.DPair d C.DNil).
Fixpoint tag_data d := match d with
 | F.Nil => C.DPair (C.DSymbol "nil") C.DNil
 | F.Sym s => tag1 "sym" (C.DSymbol s)
 | F.Num n => tag1 "num" (C.DInteger (Z.of_nat n))
 | F.TextNode s => tag1 "text" (byte_data s)
 | F.Pair a b => C.DPair (C.DSymbol "pair") (C.DPair (tag_data a) (C.DPair (tag_data b) C.DNil)) end.
Ltac start_run := unfold runs; eexists; split; [reflexivity|]; split; [reflexivity|].
Ltac small := unfold executes; exists 10; reflexivity.
Theorem bytes_correct : forall s,
 runs P "kl:buri.kl-bytes" [Text s] (C.native (byte_data s)).
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
 runs P "kl:buri.kl-node" [NativeHelpers.lift d] (C.native (tag_data d)).
Proof.
 induction d as [|s|n|s|a A b B]; start_run.
 - exists 10; reflexivity.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   small.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|]. small.
 - eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=false); [small|].
   eapply branch with (flag:=true); [small|].
   eapply primitive_call.
   + constructor; [apply literal|constructor; [|constructor]].
     eapply call; [constructor; [small|constructor]|apply bytes_correct].
   + reflexivity.
   + reflexivity.
 - eapply branch with (flag:=false); [small|].
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
Lemma decimal_agrees : forall n, n <= 256 -> spelling (Z.of_nat n) = CaptureTag.decimal n.
Proof. intros n H; do 257 (destruct n; [vm_compute; reflexivity|]); lia. Qed.
Lemma bytes_wire : forall s, C.wire (byte_data s) = CaptureTag.bytes s.
Proof.
 induction s as [|c s IH]; [reflexivity|]. cbn [byte_data C.wire CaptureTag.bytes].
 rewrite decimal_agrees by (pose proof (nat_ascii_bounded c); lia). rewrite IH; reflexivity.
Qed.
Theorem tag_wire : forall d, CaptureTag.admitted d -> C.wire (tag_data d) = CaptureTag.tag d.
Proof.
 induction d; intro H; cbn [tag_data tag1 C.wire CaptureTag.tag CaptureTag.envelope CaptureTag.one]; try reflexivity.
 - rewrite decimal_agrees by exact H; reflexivity.
 - rewrite bytes_wire; reflexivity.
 - destruct H as [A B]; rewrite IHd1,IHd2 by assumption; reflexivity.
Qed.
Theorem adapter_machine : forall d, exists steps,
 NativeRuntime.invoke steps program "kl:buri.kl-node" [NativeHelpers.lift d] = Returned (C.native (tag_data d)).
Proof.
 intros d; destruct (runs_run _ _ _ _ (node_correct d)) as [n H].
 eapply NativeSimulation.run_invoke; exact H.
Qed.
Theorem adapter_wire_roundtrip : forall d, CaptureTag.admitted d ->
 exists tag_steps wire_steps,
 NativeRuntime.invoke tag_steps program "kl:buri.kl-node" [NativeHelpers.lift d] = Returned (C.native (tag_data d)) /\
 NativeRuntime.invoke wire_steps SealedInput.sealed_native_program "kl:buri.wire" [C.native (tag_data d)] =
 Returned (Text (Wire.capture (CaptureTag.tag d))) /\
 F.untag (CaptureTag.depth d) (CaptureTag.tag d) = Some d.
Proof.
 intros d H. destruct (adapter_machine d) as [n N]. destruct (C.machine_correct (tag_data d)) as [m M].
 exists n,m; split; [exact N|]. split.
 - rewrite tag_wire in M by exact H; exact M.
 - apply CaptureTag.tag_roundtrip; auto.
Qed.
End AdapterCorrect.
