(* Canonical inert data transport. The parser and all correspondence claims
   are checked by Rocq; no generated source AST is trusted here. *)
From Coq Require Import List Bool Arith Lia Ascii String.
Import ListNotations.
Open Scope list_scope.
Module Wire.
Inductive datum := Nil | Atom : bool -> string -> datum | Cons : datum -> datum -> datum.
Definition char_bits (c : ascii) : list bool :=
 match c with Ascii a b c d e f g h => [a;b;c;d;e;f;g;h] end.
Fixpoint string_bits (s : string) : list bool :=
 match s with
 | EmptyString => [false]
 | String c rest => true :: char_bits c ++ string_bits rest
 end.
Fixpoint encode (d : datum) : list bool :=
 match d with
 | Nil => [false;false]
 | Atom tag s => false :: true :: tag :: string_bits s
 | Cons a b => true :: encode a ++ encode b
 end.
Fixpoint read_string (fuel : nat) (bs : list bool) : option (string * list bool) :=
 match fuel with
 | O => None
 | S n => match bs with
   | false :: rest => Some (EmptyString, rest)
   | true :: a::b::c::d::e::f::g::h::rest =>
     match read_string n rest with
     | Some (s, tail) => Some (String (Ascii a b c d e f g h) s, tail)
     | None => None
     end
   | _ => None
   end
 end.
Lemma string_bits_length : forall s,
 List.length (string_bits s) = 1 + 9 * String.length s.
Proof. induction s; simpl; [lia|]. destruct a; simpl; lia. Qed.
Lemma read_string_complete : forall s n tail,
 String.length s < n -> read_string n (string_bits s ++ tail) = Some (s,tail).
Proof.
 induction s as [|c s IH]; intros n tail H; destruct n; try lia.
 - reflexivity.
 - destruct c; simpl in *. rewrite IH by lia. reflexivity.
Qed.
Lemma read_string_sound : forall n bs s tail,
 read_string n bs = Some (s,tail) -> bs = string_bits s ++ tail.
Proof.
 induction n as [|n IH]; intros bs s tail H; [discriminate|].
 destruct bs as [|b rest]; [discriminate|]. destruct b.
 - destruct rest as [|a [|b [|c [|d [|e [|f [|g [|h rest]]]]]]]]; try discriminate.
   simpl in H. destruct (read_string n rest) as [[v t]|] eqn:E; try discriminate.
   inversion H; subst. simpl. rewrite (IH _ _ _ E). reflexivity.
 - inversion H; subst; reflexivity.
Qed.
Fixpoint read (fuel : nat) (bs : list bool) : option (datum * list bool) :=
 match fuel with
 | O => None
 | S n => match bs with
   | false :: false :: rest => Some (Nil,rest)
   | false :: true :: tag :: rest =>
     match read_string (S (List.length rest)) rest with
     | Some (s,tail) => Some (Atom tag s,tail) | None => None end
   | true :: rest =>
     match read n rest with
     | Some (a,mid) => match read n mid with
                      | Some (b,tail) => Some (Cons a b,tail) | None => None end
     | None => None end
   | _ => None
   end
 end.
Fixpoint height d := match d with Cons a b => S (Nat.max (height a) (height b)) | _ => 1 end.
Lemma read_complete : forall d n tail,
 height d <= n -> read n (encode d ++ tail) = Some (d,tail).
Proof.
 induction d as [|tag s|a IHa b IHb]; intros n tail H; destruct n; try (simpl in H; lia).
 - reflexivity.
 - cbn [encode List.app read]. rewrite read_string_complete; [reflexivity|].
   rewrite app_length, string_bits_length. lia.
 - cbn [encode List.app read]. rewrite <- app_assoc. rewrite IHa, IHb; try reflexivity;
   simpl in H; lia.
Qed.
Lemma read_sound : forall n bs d tail,
 read n bs = Some (d,tail) -> bs = encode d ++ tail.
Proof.
 induction n as [|n IH]; intros bs d tail H; [discriminate|].
 destruct bs as [|b rest]; [discriminate|]. destruct b.
 - cbn [read] in H. destruct (read n rest) as [[a mid]|] eqn:E; try discriminate.
   destruct (read n mid) as [[c last]|] eqn:F; try discriminate.
   inversion H; subst. cbn [encode List.app]. rewrite (IH _ _ _ E), (IH _ _ _ F).
   rewrite app_assoc. reflexivity.
 - destruct rest as [|b rest]; [discriminate|]. destruct b.
   + destruct rest as [|tag rest]; [discriminate|]. cbn [read] in H.
     destruct (read_string (S (List.length rest)) rest) as [[s last]|] eqn:E; try discriminate.
     inversion H; subst. cbn [encode List.app]. rewrite (read_string_sound _ _ _ _ E). reflexivity.
   + inversion H; subst; reflexivity.
Qed.
Lemma height_fits : forall d, height d <= List.length (encode d).
Proof.
 induction d; simpl.
 - lia.
 - rewrite string_bits_length; lia.
 - rewrite app_length; lia.
Qed.
Definition decode bs :=
 match read (S (List.length bs)) bs with
 | Some (d,[]) => Some d | _ => None end.
Theorem decode_encode : forall d, decode (encode d) = Some d.
Proof.
 intros d; unfold decode. replace (encode d) with (encode d ++ []) at 2 by apply app_nil_r.
 rewrite read_complete by (pose proof (height_fits d); lia). reflexivity.
Qed.
Theorem decode_exact : forall bs d, decode bs = Some d -> encode d = bs.
Proof.
 intros bs d H; unfold decode in H.
 destruct (read (S (List.length bs)) bs) as [[v tail]|] eqn:E; try discriminate.
 destruct tail; try discriminate. inversion H; subst.
 pose proof (read_sound _ _ _ _ E). rewrite app_nil_r in H0. symmetry; exact H0.
Qed.
Theorem encode_injective : forall a b, encode a = encode b -> a = b.
Proof. intros a b H; pose proof (decode_encode a); rewrite H, decode_encode in H0; congruence. Qed.

Fixpoint bit_text (bs : list bool) : string :=
 match bs with [] => EmptyString | b::rest => String (if b then "1"%char else "0"%char) (bit_text rest) end.
Fixpoint text_bits (s : string) : option (list bool) :=
 match s with
 | EmptyString => Some []
 | String c rest =>
   match text_bits rest with
   | Some bs => if ascii_dec c "0"%char then Some (false::bs)
                else if ascii_dec c "1"%char then Some (true::bs) else None
   | None => None end
 end.
Lemma text_roundtrip : forall bs, text_bits (bit_text bs) = Some bs.
Proof. induction bs; simpl; auto. rewrite IHbs; destruct a; reflexivity. Qed.
Lemma text_exact : forall s bs, text_bits s = Some bs -> bit_text bs = s.
Proof.
 induction s; intros bs H; simpl in H.
 - inversion H; reflexivity.
 - destruct (text_bits s) as [tail|] eqn:E; try discriminate.
   destruct (ascii_dec a "0"%char); subst.
   + inversion H; subst; simpl. rewrite (IHs _ eq_refl); reflexivity.
   + destruct (ascii_dec a "1"%char); try discriminate; subst.
     inversion H; subst; simpl. rewrite (IHs _ eq_refl); reflexivity.
Qed.
Definition capture d := bit_text (encode d).
Definition decode_text s := match text_bits s with Some bs => decode bs | None => None end.
Theorem capture_roundtrip : forall d, decode_text (capture d) = Some d.
Proof. intros; unfold decode_text, capture; rewrite text_roundtrip, decode_encode; reflexivity. Qed.
Theorem capture_exact : forall s d, decode_text s = Some d -> capture d = s.
Proof.
 intros s d H; unfold decode_text in H. destruct (text_bits s) as [bs|] eqn:E; try discriminate.
 unfold capture. rewrite (decode_exact _ _ H). apply text_exact; exact E.
Qed.
End Wire.
