(* Admission of the actual paired KLambda/Scheme load record. Syntax is inert;
   unsupported forms fail closed. Composite primitive contracts are explicit. *)
From Coq Require Import List String Bool.
From Buri Require Import Wire Encoder EncoderNames EncoderFrontend EncoderScheme.
Import ListNotations.
Open Scope string_scope.
Module ObservedEncoder.
Import Encoder.Encoder EncoderNames.EncoderNames EncoderFrontend.EncoderFrontend.
Definition unary_s p s := Some (NPrimitive p (NVariable s) unused).
Fixpoint decode fuel d : option named := match fuel with
| O => None
| S n => match d with
  | TextNode s => Some (NLiteral (Text s))
  | Num k => Some (NLiteral (Number k))
  | Sym s => Some (NVariable s)
  | _ => match elements d with
    | Some [Sym "if";c;a;b] => match decode n c,decode n a,decode n b with
        Some x,Some y,Some z => Some (NBranch x y z) | _,_,_ => None end
    | Some [Sym "let";bindings;term] =>
      (* The exact compiler expansion of tlstr; no arbitrary effect erasure. *)
      match elements bindings,elements term with
      | Some [binding],Some [Sym "substring";Sym t;Num 1;len] =>
        match elements binding,elements len with
        | Some [Sym local;Sym x],Some [Sym "string-length";Sym u] =>
          if andb (String.eqb local t) (String.eqb local u) then unary_s Tail x else None
        | _,_ => None end
      | Some [binding],_ => match elements binding with
        | Some [Sym x;a] => binary (NBind x) (decode n a) (decode n term)
        | _ => None end
      | _,_ => None end
    | Some [Sym "let*";bindings;term] => decode_bindings n bindings term
    | Some [Sym "string-append";a;b] => binary (NPrimitive Cat) (decode n a) (decode n b)
    | Some [Sym "eqv?";Sym x;Num O] => unary_s Zero x
    | Some [Sym "equal?";Sym x;TextNode ""] => unary_s Empty x
    | Some [Sym "null?";Sym x] => unary_s IsNil x
    | Some [Sym "kl:=";Sym x;product] => match elements product with
      Some [Sym "*";Sym y;Num 2] => Some (NPrimitive Even (NVariable x) (NVariable y)) | _ => None end
    | Some [Sym "kl:floor";quotient] => match elements quotient with
      Some [Sym "non-rational-/";Sym x;Num 2] => unary_s Half x | _ => None end
    | Some [Sym "-";Sym x;Num 1] => unary_s Prev x
    | Some [Sym "char->integer";outer] => match elements outer with
      | Some [Sym "string-ref";str;Num O] => match elements str with
        | Some [Sym "string";inner] => match elements inner with
          | Some [Sym "string-ref";Sym x;Num O] => unary_s Code x | _ => None end
        | _ => None end
      | _ => None end
    | Some [Sym "and";low;high] => match elements low,elements high with
      | Some [Sym ">=";Sym x;Num O],Some [Sym "<";Sym y;Num 256] =>
        if String.eqb x y then unary_s ByteRange x else None
      | _,_ => None end
    | Some [Sym "pair?";Sym x] => unary_s IsPair x
    | Some [Sym "car";Sym x] => unary_s Head x
    | Some [Sym "cdr";Sym x] => unary_s Rest x
    | Some [Sym "kl:_scm.assert-boolean";a] => match elements a with
      | Some [Sym "kl:buri.exact-integer?";Sym x] => unary_s IsNumber x | _ => None end
    | Some [Sym "kl:symbol?";Sym x] => unary_s IsSymbol x
    | Some [Sym "kl:str";Sym x] => unary_s Spelling x
    | Some [Sym "kl:buri.wire-byte";a;b] => binary (NInvoke Byte) (decode n a) (decode n b)
    | Some [Sym "kl:buri.wire-string";a] => binary (NInvoke Str) (decode n a) (Some unused)
    | Some [Sym "kl:buri.wire";a] => binary (NInvoke Datum) (decode n a) (Some unused)
    | Some [Sym "error";owner;TextNode message] => match elements owner with
      | Some [Sym "quote";Sym _] => Some (NError message) | _ => None end
    | _ => None end
  end end
with decode_bindings fuel bindings term : option named := match fuel with
| O => None
| S n => match bindings with
  | Nil => decode n term
  | Pair binding rest => match elements binding with
    | Some [Sym x;a] => binary (NBind x) (decode n a) (decode_bindings n rest term)
    | _ => None end
  | _ => None end end.
Definition decode_definition fuel f d : option definition := match elements d with
| Some [Sym "define";signature;term] => match signature with
  | Pair (Sym name) args => if String.eqb name ("kl:" ++ function_name f)
    then match params f args,decode fuel term with
      Some names,Some e => Some (Defn names e) | _,_ => None end else None
  | _ => None end
| _ => None end.
Definition target_ok f def := match resolve (parameters def) (expression def) with
| Some e => if expr_eq_dec e (EncoderScheme.target f) then true else false
| None => false end.
Definition check_pair fuel f record : option (definition * definition) := match elements record with
| Some [source;target] => match EncoderFrontend.decode_definition fuel f source,decode_definition fuel f target with
  | Some a,Some b => if andb (definition_ok f a) (target_ok f b) then Some (a,b) else None
  | _,_ => None end
| _ => None end.
Definition pair_valid fuel f record a b := exists source target,
 elements record = Some [source;target] /\
 EncoderFrontend.decode_definition fuel f source = Some a /\
 decode_definition fuel f target = Some b /\
 resolve (parameters a) (expression a) = Some (body f) /\
 resolve (parameters b) (expression b) = Some (EncoderScheme.target f).
Lemma target_ok_sound : forall f b, target_ok f b = true ->
 resolve (parameters b) (expression b) = Some (EncoderScheme.target f).
Proof.
 intros f b H. unfold target_ok in H.
 destruct (resolve (parameters b) (expression b)) as [e|] eqn:E; try discriminate.
 destruct (expr_eq_dec e (EncoderScheme.target f)); try discriminate; subst; reflexivity.
Qed.
Theorem check_pair_sound : forall fuel f record a b,
 check_pair fuel f record = Some (a,b) -> pair_valid fuel f record a b.
Proof.
 intros fuel f record a b H. unfold check_pair in H.
 destruct (elements record) as [nodes|] eqn:E; try discriminate.
 destruct nodes as [|src [|tgt [|extra rest]]]; try discriminate.
 destruct (EncoderFrontend.decode_definition fuel f src) as [da|] eqn:A; try discriminate.
 destruct (decode_definition fuel f tgt) as [db|] eqn:B; try discriminate.
 destruct (definition_ok f da && target_ok f db) eqn:V; try discriminate.
 inversion H; subst. apply andb_true_iff in V as [VA VB].
 exists src,tgt. repeat split; auto using definition_ok_sound, target_ok_sound.
Qed.
Definition check_program fuel root : option (program * program) := match elements root with
| Some [a;b;c] => match check_pair fuel Byte a,check_pair fuel Str b,check_pair fuel Datum c with
  | Some (sa,ta),Some (sb,tb),Some (sc,tc) => Some (assemble sa sb sc,assemble ta tb tc)
  | _,_,_ => None end
| _ => None end.
Definition coverage fuel root sp tp := exists a b c sa sb sc ta tb tc,
 elements root = Some [a;b;c] /\
 pair_valid fuel Byte a sa ta /\ pair_valid fuel Str b sb tb /\ pair_valid fuel Datum c sc tc /\
 sp = assemble sa sb sc /\ tp = assemble ta tb tc.
Theorem check_program_coverage : forall fuel root sp tp,
 check_program fuel root = Some (sp,tp) -> coverage fuel root sp tp.
Proof.
 intros fuel root sp tp H. unfold check_program in H.
 destruct (elements root) as [nodes|] eqn:E; try discriminate.
 destruct nodes as [|a [|b [|c [|extra rest]]]]; try discriminate.
 destruct (check_pair fuel Byte a) as [[sa ta]|] eqn:A; try discriminate.
 destruct (check_pair fuel Str b) as [[sb tb]|] eqn:B; try discriminate.
 destruct (check_pair fuel Datum c) as [[sc tc]|] eqn:C; try discriminate.
 inversion H; subst. exists a,b,c,sa,sb,sc,ta,tb,tc.
 repeat split; auto; eapply check_pair_sound; eauto.
Qed.
Definition target_resolves (tp : program) := forall f,
 resolve (parameters (tp f)) (expression (tp f)) = Some (EncoderScheme.target f).
Theorem coverage_resolves : forall fuel root sp tp,
 coverage fuel root sp tp -> program_resolves sp /\ target_resolves tp.
Proof.
 intros fuel root sp tp [a [b [c [sa [sb [sc [ta [tb [tc [E [A [B [C [S T]]]]]]]]]]]]]].
 destruct A as [asrc [atgt [AE [AS [AT [AP AQ]]]]]].
 destruct B as [bsrc [btgt [BE [BS [BT [BP BQ]]]]]].
 destruct C as [csrc [ctgt [CE [CS [CT [CP CQ]]]]]].
 subst sp tp. split; intros f; destruct f; assumption.
Qed.
Definition capture_program fuel raw : option (node * program * program) := match raw with
| Wire.Cons (Wire.Atom false profile) (Wire.Cons tagged Wire.Nil) =>
  if String.eqb profile "buri-observed-encoder-1" then match untag fuel tagged with Some root => match check_program fuel root with
    Some (sp,tp) => Some (root,sp,tp) | None => None end | None => None end else None
| _ => None end.
Definition check_capture fuel bits : option (Wire.datum * node * program * program) :=
 match Wire.decode_text bits with Some raw => match capture_program fuel raw with
  Some (root,sp,tp) => Some (raw,root,sp,tp) | None => None end | None => None end.
Definition accepted fuel bits := match check_capture fuel bits with Some _ => true | None => false end.
Theorem capture_coverage : forall fuel raw root sp tp,
 capture_program fuel raw = Some (root,sp,tp) -> coverage fuel root sp tp.
Proof.
 intros fuel raw root sp tp H. unfold capture_program in H.
 destruct raw as [| |head tail]; try discriminate.
 destruct head as [|tag profile|]; try discriminate. destruct tag; try discriminate.
 destruct tail as [| |tagged rest]; try discriminate. destruct rest; try discriminate.
 destruct (String.eqb profile "buri-observed-encoder-1"); try discriminate.
 destruct (untag fuel tagged) as [r|] eqn:U; try discriminate.
 destruct (check_program fuel r) as [[s t]|] eqn:P; try discriminate.
 inversion H; subst; eapply check_program_coverage; exact P.
Qed.
Theorem accepted_sound : forall fuel bits, accepted fuel bits = true ->
 exists raw root sp tp, check_capture fuel bits = Some (raw,root,sp,tp) /\
 Wire.capture raw = bits /\ coverage fuel root sp tp /\ program_resolves sp /\ target_resolves tp.
Proof.
 intros fuel bits H. unfold accepted,check_capture in H.
 destruct (Wire.decode_text bits) as [raw|] eqn:D; try discriminate.
 destruct (capture_program fuel raw) as [[[root sp] tp]|] eqn:C; try discriminate.
 pose proof (capture_coverage _ _ _ _ _ C) as CV.
 destruct (coverage_resolves _ _ _ _ CV) as [S T].
 exists raw,root,sp,tp. split; [unfold check_capture; rewrite D,C; reflexivity |].
 repeat split; auto. apply Wire.capture_exact; exact D.
Qed.
(* Executing a decoded target uses its resolved lexical body and the complete
   resolved recursive function table. None cannot manufacture a successful run. *)
Definition resolved_table (tp : program) f :=
 match resolve (parameters (tp f)) (expression (tp f)) with Some e => e | None => Fail "unresolved" end.
Lemma exec_table : forall p q env e v,
 (forall f, p f = q f) -> EncoderScheme.exec p env e v -> EncoderScheme.exec q env e v.
Proof.
 intros p q env e v EQ H; induction H; eauto using EncoderScheme.exec.
 eapply EncoderScheme.ECall; eauto. rewrite <- EQ. exact IHexec3.
Qed.
Theorem paired_execution : forall sp tp,
 program_resolves sp -> target_resolves tp -> forall f x y n v,
 EncoderNames.eval n sp (arguments (parameters (sp f)) x y) (expression (sp f)) = Returned v ->
 EncoderScheme.exec (resolved_table tp) [x;y] (resolved_table tp f) v.
Proof.
 intros sp tp S T f x y n v H.
 rewrite program_preserves in H by exact S.
 assert (E : forall g, resolved_table tp g = EncoderScheme.target g).
 { intros g; unfold resolved_table; rewrite T; reflexivity. }
 rewrite E. eapply exec_table; [intros g; symmetry; apply E |].
 apply EncoderScheme.anf_preserves. eapply EncoderScheme.evaluator_exec; exact H.
Qed.
Theorem checked_execution : forall tp, target_resolves tp -> forall d,
 EncoderScheme.exec (resolved_table tp) [Data d;Number 0] (resolved_table tp Datum) (Text (Wire.capture d)) /\
 (forall v, EncoderScheme.exec (resolved_table tp) [Data d;Number 0] (resolved_table tp Datum) v -> v = Text (Wire.capture d)).
Proof.
 intros tp H d. assert (E : forall f, resolved_table tp f = EncoderScheme.target f).
 { intros f; unfold resolved_table. rewrite H. reflexivity. }
 assert (R : EncoderScheme.exec (resolved_table tp) [Data d;Number 0] (resolved_table tp Datum) (Text (Wire.capture d))).
 { rewrite E. eapply exec_table; [intros f; symmetry; apply E | apply EncoderScheme.encoder_target_total]. }
 split; [exact R |]. intros v V. eapply EncoderScheme.exec_deterministic; eauto.
Qed.
End ObservedEncoder.
