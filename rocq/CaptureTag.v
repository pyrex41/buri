(* Typed transport specification. This proves the protocol, not execution of
   the Shen adapter or provenance of the syntax supplied to it. *)
From Coq Require Import List String Ascii Arith Lia DecimalString.
From Buri Require Import Wire EncoderFrontend.
Import ListNotations.
Open Scope string_scope.
Module CaptureTag.
Import EncoderFrontend.EncoderFrontend.
Definition decimal n := NilZero.string_of_uint (Nat.to_uint n).
Definition envelope name args := Wire.Cons (Wire.Atom false name) args.
Definition one x := Wire.Cons x Wire.Nil.
Fixpoint bytes s := match s with
| EmptyString => Wire.Nil
| String c rest => Wire.Cons (Wire.Atom true (decimal (nat_of_ascii c))) (bytes rest)
end.
Fixpoint tag d := match d with
| Nil => envelope "nil" Wire.Nil
| Sym s => envelope "sym" (one (Wire.Atom false s))
| Num n => envelope "num" (one (Wire.Atom true (decimal n)))
| TextNode s => envelope "text" (one (bytes s))
| Pair a b => envelope "pair" (Wire.Cons (tag a) (one (tag b)))
end.
Fixpoint admitted d : Prop := match d with
| Num n => n <= 256
| Pair a b => admitted a /\ admitted b
| _ => True end.
Fixpoint depth d := match d with Pair a b => S (Nat.max (depth a) (depth b)) | _ => 1 end.
Lemma decimal_small : forall n, n <= 256 -> small_nat (decimal n) = Some n.
Proof.
 intros n H. do 257 (destruct n as [|n]; [vm_compute; reflexivity |]). lia.
Qed.
Theorem bytes_roundtrip : forall s, byte_string (bytes s) = Some s.
Proof.
 induction s as [|c s IH]; [reflexivity|]. cbn [bytes byte_string].
 rewrite decimal_small by (pose proof (nat_ascii_bounded c); lia).
 rewrite IH. assert (B : Nat.ltb (nat_of_ascii c) 256 = true) by
  (apply Nat.ltb_lt; apply nat_ascii_bounded). rewrite B.
 rewrite ascii_nat_embedding. reflexivity.
Qed.
Theorem tag_roundtrip : forall d fuel, admitted d -> depth d <= fuel ->
 untag fuel (tag d) = Some d.
Proof.
 induction d; intros fuel A H; destruct fuel; cbn [depth] in H; try lia;
 cbn [tag untag envelope one].
 - reflexivity.
 - reflexivity.
 - rewrite decimal_small by exact A. reflexivity.
 - rewrite bytes_roundtrip. reflexivity.
 - destruct A as [A B]. rewrite IHd1, IHd2; try assumption; try lia. reflexivity.
Qed.
Theorem tag_injective : forall a b, admitted a -> admitted b -> tag a = tag b -> a = b.
Proof.
 intros a b A B E.
 pose proof (tag_roundtrip a (Nat.max (depth a) (depth b)) A (Nat.le_max_l _ _)) as HA.
 pose proof (tag_roundtrip b (Nat.max (depth a) (depth b)) B (Nat.le_max_r _ _)) as HB.
 rewrite E in HA. rewrite HB in HA. inversion HA. reflexivity.
Qed.
Theorem wire_tag_roundtrip : forall d, admitted d ->
 exists raw, Wire.decode_text (Wire.capture (tag d)) = Some raw /\
 untag (depth d) raw = Some d.
Proof.
 intros d A. exists (tag d). split; [apply Wire.capture_roundtrip |].
 apply tag_roundtrip; auto.
Qed.
(* If the producer represents root by this protocol, acceptance is about
   exactly root. The hypothesis is deliberately explicit and auditable. *)
Theorem capture_root_exact : forall root fuel prog,
 admitted root -> depth root <= fuel ->
 capture_program fuel (envelope "buri-encoder-kl-1" (one (tag root))) = Some prog ->
 complete_program fuel root prog /\ EncoderNames.EncoderNames.program_resolves prog.
Proof.
 intros root fuel prog A D H.
 cbn [capture_program envelope one] in H.
 rewrite tag_roundtrip in H by assumption.
 split; [eapply check_program_coverage | eapply check_program_sound]; exact H.
Qed.
End CaptureTag.
