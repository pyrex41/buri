(* Named semantics for the admitted first-order encoder fragment. *)
From Coq Require Import List String.
From Buri Require Import Wire Resolve Encoder.
Import ListNotations.
Module EncoderNames.
Import Encoder.Encoder.
Inductive named :=
 | NLiteral (v : value) | NError (message : string) | NVariable (name : string)
 | NBranch (c a b : named) | NBind (name : string) (a b : named)
 | NPrimitive (p : operation) (a b : named) | NInvoke (f : function) (a b : named).
Record definition := Defn { parameters : list string; expression : named }.
Definition program := function -> definition.
Definition environment := string -> option value.
Definition update (env : environment) x v y := if string_dec y x then Some v else env y.
Definition arguments (params : list string) x y : environment := fun name =>
 match Resolve.lookup name params with Some i => nth_error [x;y] i | None => None end.
Fixpoint resolve scope e : option expr := match e with
 | NLiteral v => Some (Lit v) | NError s => Some (Fail s)
 | NVariable x => match Resolve.lookup x scope with Some i => Some (Var i) | None => None end
 | NBranch c a b => match resolve scope c,resolve scope a,resolve scope b with
     Some c',Some a',Some b' => Some (If c' a' b') | _,_,_ => None end
 | NBind x a b => match resolve scope a,resolve (x::scope) b with
     Some a',Some b' => Some (Let a' b') | _,_ => None end
 | NPrimitive p a b => match resolve scope a,resolve scope b with
     Some a',Some b' => Some (Op p a' b') | _,_ => None end
 | NInvoke f a b => match resolve scope a,resolve scope b with
     Some a',Some b' => Some (Call f a' b') | _,_ => None end
 end.
Fixpoint eval fuel (prog : program) (env : environment) e : result := match fuel with
 | O => Exhausted
 | S n => match e with
   | NLiteral v => Returned v | NError _ => Stuck
   | NVariable x => match env x with Some v => Returned v | None => Stuck end
   | NBranch c a b => match eval n prog env c with
       | Returned (Boolean true) => eval n prog env a
       | Returned (Boolean false) => eval n prog env b
       | Exhausted => Exhausted | _ => Stuck end
   | NBind x a b => match eval n prog env a with
       | Returned v => eval n prog (update env x v) b
       | Exhausted => Exhausted | _ => Stuck end
   | NPrimitive p a b => match eval n prog env a with
       | Returned x => match eval n prog env b with
           | Returned y => match primitive p x y with Some v => Returned v | None => Stuck end
           | Exhausted => Exhausted | _ => Stuck end
       | Exhausted => Exhausted | _ => Stuck end
   | NInvoke f a b => match eval n prog env a with
       | Returned x => match eval n prog env b with
           | Returned y => let def := prog f in eval n prog (arguments (parameters def) x y) (expression def)
           | Exhausted => Exhausted | _ => Stuck end
       | Exhausted => Exhausted | _ => Stuck end
   end end.
Definition corresponds scope (env : environment) stack := forall x i,
 Resolve.lookup x scope = Some i -> env x = nth_error stack i.
Lemma update_corresponds : forall scope env stack x v,
 corresponds scope env stack -> corresponds (x::scope) (update env x v) (v::stack).
Proof.
 intros scope env stack x v H y i E. cbn in E. unfold update.
 destruct (string_dec y x) as [Eq|Neq]; subst.
 - destruct (string_dec x x); try contradiction. inversion E; reflexivity.
 - destruct (Resolve.lookup y scope) as [j|] eqn:F; try discriminate.
   inversion E; subst. cbn. apply H; exact F.
Qed.
Lemma arguments_correspond : forall params x y,
 corresponds params (arguments params x y) [x;y].
Proof. intros params x y name i H. unfold arguments; rewrite H; reflexivity. Qed.
Definition program_resolves (prog : program) := forall f,
 resolve (parameters (prog f)) (expression (prog f)) = Some (body f).
Theorem resolve_preserves : forall fuel prog,
 program_resolves prog -> forall e scope env stack lowered,
 resolve scope e = Some lowered -> corresponds scope env stack ->
 eval fuel prog env e = Encoder.eval fuel stack lowered.
Proof.
 induction fuel as [|n IH]; intros prog HP e scope env stack lowered H HC; [reflexivity|].
 destruct e; cbn [resolve] in H.
 - inversion H; reflexivity.
 - inversion H; reflexivity.
 - destruct (Resolve.lookup name scope) as [i|] eqn:E; try discriminate.
   inversion H; subst. cbn [eval Encoder.eval]. rewrite (HC _ _ E); reflexivity.
 - destruct (resolve scope e1) as [c|] eqn:C; try discriminate.
   destruct (resolve scope e2) as [a|] eqn:A; try discriminate.
   destruct (resolve scope e3) as [b|] eqn:B; try discriminate.
   inversion H; subst. cbn [eval Encoder.eval].
   rewrite (IH _ HP _ _ _ _ _ C HC), (IH _ HP _ _ _ _ _ A HC), (IH _ HP _ _ _ _ _ B HC).
   reflexivity.
 - destruct (resolve scope e1) as [a|] eqn:A; try discriminate.
   destruct (resolve (name::scope) e2) as [b|] eqn:B; try discriminate.
   inversion H; subst. cbn [eval Encoder.eval]. rewrite (IH _ HP _ _ _ _ _ A HC).
   destruct (Encoder.eval n stack a); try reflexivity.
   apply (IH _ HP _ _ _ _ _ B). apply update_corresponds; exact HC.
 - destruct (resolve scope e1) as [a|] eqn:A; try discriminate.
   destruct (resolve scope e2) as [b|] eqn:B; try discriminate.
   inversion H; subst. cbn [eval Encoder.eval].
   rewrite (IH _ HP _ _ _ _ _ A HC), (IH _ HP _ _ _ _ _ B HC). reflexivity.
 - destruct (resolve scope e1) as [a|] eqn:A; try discriminate.
   destruct (resolve scope e2) as [b|] eqn:B; try discriminate.
   inversion H; subst. cbn [eval Encoder.eval].
   rewrite (IH _ HP _ _ _ _ _ A HC), (IH _ HP _ _ _ _ _ B HC).
   destruct (Encoder.eval n stack a); try reflexivity.
   destruct (Encoder.eval n stack b); try reflexivity.
   apply IH with (scope:=parameters (prog f)); auto using arguments_correspond.
Qed.
Theorem program_preserves : forall prog,
 program_resolves prog -> forall f x y fuel,
 eval fuel prog (arguments (parameters (prog f)) x y) (expression (prog f)) =
 Encoder.eval fuel [x;y] (body f).
Proof. intros; eapply resolve_preserves; eauto using arguments_correspond. Qed.
Theorem program_encoder_total : forall prog, program_resolves prog -> forall d,
 exists fuel, eval fuel prog (arguments (parameters (prog Datum)) (Data d) (Number 0))
 (expression (prog Datum)) = Returned (Text (Wire.capture d)).
Proof.
 intros prog H d. destruct (datum_correct d) as [n E]. exists n.
 rewrite program_preserves; auto.
Qed.
Theorem program_encoder_unique : forall prog, program_resolves prog -> forall d fuel v,
 eval fuel prog (arguments (parameters (prog Datum)) (Data d) (Number 0)) (expression (prog Datum)) = Returned v ->
 v = Text (Wire.capture d).
Proof.
 intros prog H d fuel v E. rewrite program_preserves in E by exact H.
 apply encoder_output_unique. exists fuel; exact E.
Qed.
End EncoderNames.
