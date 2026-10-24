(* Admission and translation validation for captured registered KLambda.
   Semantic decoding happens here, never in the Shen capture adapter. *)
From Coq Require Import List String Ascii ZArith Bool.
From Buri Require Import Wire NativeValidation Encoder EncoderNames.
Import ListNotations.
Open Scope string_scope.
Module EncoderFrontend.
Import Encoder.Encoder EncoderNames.EncoderNames.
Inductive node := Nil | Sym (s : string) | Num (n : nat) | TextNode (s : string) | Pair (a b : node).
Definition small_nat s : option nat :=
 match NativeValidation.integer s with
 | Some z => if andb (Z.leb 0 z) (Z.leb z 256) then Some (Z.to_nat z) else None
 | None => None end.
Fixpoint byte_string d : option string := match d with
 | Wire.Nil => Some ""
 | Wire.Cons (Wire.Atom true s) rest =>
   match small_nat s,byte_string rest with
   | Some n,Some tail => if Nat.ltb n 256 then Some (String (ascii_of_nat n) tail) else None
   | _,_ => None end
 | _ => None end.
Fixpoint untag fuel d : option node := match fuel with
 | O => None
 | S n => match d with
   | Wire.Cons (Wire.Atom false "nil") Wire.Nil => Some Nil
   | Wire.Cons (Wire.Atom false "sym") (Wire.Cons (Wire.Atom false s) Wire.Nil) => Some (Sym s)
   | Wire.Cons (Wire.Atom false "num") (Wire.Cons (Wire.Atom true s) Wire.Nil) =>
       match small_nat s with Some k => Some (Num k) | None => None end
   | Wire.Cons (Wire.Atom false "text") (Wire.Cons bytes Wire.Nil) =>
       match byte_string bytes with Some s => Some (TextNode s) | None => None end
   | Wire.Cons (Wire.Atom false "pair") (Wire.Cons a (Wire.Cons b Wire.Nil)) =>
       match untag n a,untag n b with Some x,Some y => Some (Pair x y) | _,_ => None end
   | _ => None end end.
Fixpoint elements d : option (list node) := match d with
 | Nil => Some []
 | Pair a b => match elements b with Some bs => Some (a::bs) | None => None end
 | _ => None end.
Fixpoint variable_tail s := match s with
 | EmptyString => true
 | String c tail => andb
   (orb (NativeValidation.letter c) (orb (Ascii.eqb c "_"%char)
    (andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57)))) (variable_tail tail)
 end.
Definition variable_ok s := match s with
 | EmptyString => false
 | String c tail => andb (andb (Nat.leb 65 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 90)) (variable_tail tail)
 end.
Definition variable s := if variable_ok s then Some (NVariable s) else None.
Definition unused := NLiteral (Number 0).
Definition unary_var p s := match variable s with Some v => Some (NPrimitive p v unused) | None => None end.
Definition binary (op : named -> named -> named) (a b : option named) := match a,b with Some x,Some y => Some (op x y) | _,_ => None end.
(* Compound primitive contracts are recognized only with the exact shown
   constants and variable operands. In particular the range test cannot hide
   duplicated effects or tests of two different values. *)
Fixpoint decode fuel d : option named := match fuel with
 | O => None
 | S n => match d with
   | TextNode s => Some (NLiteral (Text s))
   | Num k => Some (NLiteral (Number k))
   | Sym s => variable s
   | _ => match elements d with
     | Some [Sym "if";c;a;b] => match decode n c,decode n a,decode n b with
         Some c',Some a',Some b' => Some (NBranch c' a' b') | _,_,_ => None end
     | Some [Sym "let";Sym x;a;b] => if variable_ok x
         then binary (NBind x) (decode n a) (decode n b) else None
     | Some [Sym "simple-error";TextNode s] => Some (NError s)
     | Some [Sym "cn";a;b] => binary (NPrimitive Cat) (decode n a) (decode n b)
     | Some [Sym "=";Sym x;Num O] => unary_var Zero x
     | Some [Sym "=";Sym x;TextNode ""] => unary_var Empty x
     | Some [Sym "=";Sym x;Nil] => unary_var IsNil x
     | Some [Sym "=";Sym x;product] => match elements product with
         Some [Sym "*";Sym y;Num 2] => binary (NPrimitive Even) (variable x) (variable y)
         | _ => None end
     | Some [Sym "floor";quotient] => match elements quotient with
         Some [Sym "/";Sym x;Num 2] => unary_var Half x | _ => None end
     | Some [Sym "-";Sym x;Num 1] => unary_var Prev x
     | Some [Sym "string->n";first] => match elements first with
         Some [Sym "pos";Sym x;Num O] => unary_var Code x | _ => None end
     | Some [Sym "and";low;high] => match elements low,elements high with
         Some [Sym ">=";Sym x;Num O],Some [Sym "<";Sym y;Num 256] =>
           if String.eqb x y then unary_var ByteRange x else None
         | _,_ => None end
     | Some [Sym "tlstr";Sym x] => unary_var Tail x
     | Some [Sym "cons?";Sym x] => unary_var IsPair x
     | Some [Sym "hd";Sym x] => unary_var Head x
     | Some [Sym "tl";Sym x] => unary_var Rest x
     | Some [Sym "buri.exact-integer?";Sym x] => unary_var IsNumber x
     | Some [Sym "symbol?";Sym x] => unary_var IsSymbol x
     | Some [Sym "str";Sym x] => unary_var Spelling x
     | Some [Sym "buri.wire-byte";a;b] => binary (NInvoke Byte) (decode n a) (decode n b)
     | Some [Sym "buri.wire-string";a] => binary (NInvoke Str) (decode n a) (Some unused)
     | Some [Sym "buri.wire";a] => binary (NInvoke Datum) (decode n a) (Some unused)
     | _ => None end
   end end.
Definition params f d : option (list string) := match f,elements d with
 | Byte,Some [Sym x;Sym y] =>
     if andb (andb (variable_ok x) (variable_ok y)) (negb (String.eqb x y)) then Some [x;y] else None
 | Str,Some [Sym x] | Datum,Some [Sym x] => if variable_ok x then Some [x] else None
 | _,_ => None end.
Definition decode_definition fuel f d : option definition := match elements d with
 | Some [Sym "defun";Sym name;args;term] =>
   if String.eqb name (function_name f) then
     match params f args,decode fuel term with
     | Some names,Some e => Some (Defn names e) | _,_ => None end
   else None
 | _ => None end.
Definition datum_eq_dec : forall a b : Wire.datum, {a=b}+{a<>b}.
Proof. decide equality; apply string_dec || decide equality. Defined.
Definition value_eq_dec : forall a b : value, {a=b}+{a<>b}.
Proof. decide equality; try apply string_dec; try apply Nat.eq_dec; try apply datum_eq_dec; decide equality. Defined.
Definition expr_eq_dec : forall a b : expr, {a=b}+{a<>b}.
Proof. decide equality; try apply string_dec; try apply Nat.eq_dec; try apply value_eq_dec; decide equality. Defined.
Definition definition_ok f def := match resolve (parameters def) (expression def) with
 | Some e => if expr_eq_dec e (body f) then true else false | None => false end.
Lemma definition_ok_sound : forall f def, definition_ok f def = true ->
 resolve (parameters def) (expression def) = Some (body f).
Proof.
 intros f def H; unfold definition_ok in H.
 destruct (resolve (parameters def) (expression def)) as [e|] eqn:E; try discriminate.
 destruct (expr_eq_dec e (body f)); try discriminate; subst; reflexivity.
Qed.
Definition assemble a b c : program := fun f => match f with Byte => a | Str => b | Datum => c end.
Definition check_program fuel root : option program := match elements root with
 | Some [a;b;c] => match decode_definition fuel Byte a,decode_definition fuel Str b,decode_definition fuel Datum c with
   | Some da,Some db,Some dc => if andb (definition_ok Byte da) (andb (definition_ok Str db) (definition_ok Datum dc))
       then Some (assemble da db dc) else None
   | _,_,_ => None end
 | _ => None end.
Theorem check_program_sound : forall fuel root prog,
 check_program fuel root = Some prog -> program_resolves prog.
Proof.
 intros fuel root prog H. unfold check_program in H.
 destruct (elements root) as [nodes|]; try discriminate.
 destruct nodes as [|a [|b [|c [|extra rest]]]]; try discriminate.
 destruct (decode_definition fuel Byte a) as [da|] eqn:A; try discriminate.
 destruct (decode_definition fuel Str b) as [db|] eqn:B; try discriminate.
 destruct (decode_definition fuel Datum c) as [dc|] eqn:C; try discriminate.
 destruct (definition_ok Byte da && (definition_ok Str db && definition_ok Datum dc)) eqn:E; try discriminate.
 inversion H; subst. apply andb_true_iff in E as [EA E]. apply andb_true_iff in E as [EB EC].
 intros f; destruct f; cbn [assemble]; apply definition_ok_sound; assumption.
Qed.
Definition complete_program fuel root prog := exists a b c da db dc,
 elements root = Some [a;b;c] /\
 decode_definition fuel Byte a = Some da /\
 decode_definition fuel Str b = Some db /\
 decode_definition fuel Datum c = Some dc /\ prog = assemble da db dc.
Theorem check_program_coverage : forall fuel root prog,
 check_program fuel root = Some prog -> complete_program fuel root prog.
Proof.
 intros fuel root prog H. unfold check_program in H.
 destruct (elements root) as [nodes|] eqn:E; try discriminate.
 destruct nodes as [|a [|b [|c [|extra rest]]]]; try discriminate.
 destruct (decode_definition fuel Byte a) as [da|] eqn:A; try discriminate.
 destruct (decode_definition fuel Str b) as [db|] eqn:B; try discriminate.
 destruct (decode_definition fuel Datum c) as [dc|] eqn:C; try discriminate.
 destruct (definition_ok Byte da && (definition_ok Str db && definition_ok Datum dc)); try discriminate.
 inversion H; subst. exists a,b,c,da,db,dc. repeat split; assumption || reflexivity.
Qed.
Definition capture_program fuel raw : option program := match raw with
 | Wire.Cons (Wire.Atom false profile) (Wire.Cons tagged Wire.Nil) =>
     if String.eqb profile "buri-encoder-kl-1" then
       match untag fuel tagged with Some root => check_program fuel root | None => None end
     else None
 | _ => None end.
Definition check_capture fuel bits : option (Wire.datum * program) :=
 match Wire.decode_text bits with
 | Some raw => match capture_program fuel raw with Some prog => Some (raw,prog) | None => None end
 | None => None end.
Definition accepted fuel bits := match check_capture fuel bits with Some _ => true | None => false end.
Lemma capture_program_sound : forall fuel raw prog,
 capture_program fuel raw = Some prog -> program_resolves prog.
Proof.
 intros fuel raw prog H. unfold capture_program in H.
 destruct raw as [| |head tail]; try discriminate.
 destruct head as [|tag profile|]; try discriminate.
 destruct tag; try discriminate.
 destruct tail as [| |tagged rest]; try discriminate.
 destruct rest; try discriminate.
 destruct (String.eqb profile "buri-encoder-kl-1"); try discriminate.
 destruct (untag fuel tagged) as [root|] eqn:E; try discriminate.
 eapply check_program_sound; exact H.
Qed.
Definition capture_coverage fuel raw prog := exists tagged root,
 raw = Wire.Cons (Wire.Atom false "buri-encoder-kl-1") (Wire.Cons tagged Wire.Nil) /\
 untag fuel tagged = Some root /\ complete_program fuel root prog.
Theorem capture_program_coverage : forall fuel raw prog,
 capture_program fuel raw = Some prog -> capture_coverage fuel raw prog.
Proof.
 intros fuel raw prog H. unfold capture_program in H.
 destruct raw as [| |head tail]; try discriminate.
 destruct head as [|tag profile|]; try discriminate.
 destruct tag; try discriminate.
 destruct tail as [| |tagged rest]; try discriminate.
 destruct rest; try discriminate.
 destruct (String.eqb profile "buri-encoder-kl-1") eqn:P; try discriminate.
 apply String.eqb_eq in P; subst profile.
 destruct (untag fuel tagged) as [root|] eqn:E; try discriminate.
 exists tagged,root. split; [reflexivity |]. split; [exact E |].
 eapply check_program_coverage; exact H.
Qed.
Theorem check_capture_coverage : forall fuel bits raw prog,
 check_capture fuel bits = Some (raw,prog) -> capture_coverage fuel raw prog.
Proof.
 intros fuel bits raw prog H. unfold check_capture in H.
 destruct (Wire.decode_text bits) as [data|]; try discriminate.
 destruct (capture_program fuel data) as [p|] eqn:P; try discriminate.
 inversion H; subst. eapply capture_program_coverage; exact P.
Qed.
Theorem check_capture_sound : forall fuel bits raw prog,
 check_capture fuel bits = Some (raw,prog) -> Wire.capture raw = bits /\ program_resolves prog.
Proof.
 intros fuel bits raw prog H. unfold check_capture in H.
 destruct (Wire.decode_text bits) as [data|] eqn:D; try discriminate.
 destruct (capture_program fuel data) as [p|] eqn:P; try discriminate.
 inversion H; subst. split; [apply Wire.capture_exact; exact D |].
 eapply capture_program_sound; exact P.
Qed.
Theorem accepted_sound : forall fuel bits, accepted fuel bits = true ->
 exists raw prog, check_capture fuel bits = Some (raw,prog) /\
 Wire.capture raw = bits /\ program_resolves prog.
Proof.
 intros fuel bits H. unfold accepted in H.
 destruct (check_capture fuel bits) as [[raw prog]|] eqn:E; try discriminate.
 exists raw,prog. split; [reflexivity | apply (check_capture_sound _ _ _ _ E)].
Qed.
Theorem accepted_execution : forall fuel bits, accepted fuel bits = true ->
 exists raw prog, check_capture fuel bits = Some (raw,prog) /\
 capture_coverage fuel raw prog /\
 (forall f x y n, EncoderNames.eval n prog (arguments (parameters (prog f)) x y) (expression (prog f)) =
    Encoder.eval n [x;y] (body f)) /\
 (forall d, exists n, EncoderNames.eval n prog (arguments (parameters (prog Datum)) (Data d) (Number 0))
    (expression (prog Datum)) = Returned (Text (Wire.capture d))) /\
 (forall d n v, EncoderNames.eval n prog (arguments (parameters (prog Datum)) (Data d) (Number 0))
    (expression (prog Datum)) = Returned v -> v = Text (Wire.capture d)).
Proof.
 intros fuel bits H. destruct (accepted_sound _ _ H) as [raw [prog [E [W P]]]].
 exists raw,prog. split; [exact E |]. split; [eapply check_capture_coverage; exact E |].
 split; [apply program_preserves; exact P |].
 split; [apply program_encoder_total; exact P | apply program_encoder_unique; exact P].
Qed.
End EncoderFrontend.
