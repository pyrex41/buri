(* Source-linked first-order Shen fragment. Primitive operations have explicit
   mathematical contracts; this is not a proof of the host or define compiler. *)
From Coq Require Import List String Ascii Bool Arith Lia.
From Buri Require Import Wire.
Import ListNotations.
Open Scope string_scope.
Module Encoder.
Inductive value := Text (s : string) | Number (n : nat) | Boolean (b : bool) | Data (d : Wire.datum).
Inductive function := Byte | Str | Datum.
Inductive operation := Cat | Zero | Half | Even | Prev | Empty | Code | Tail
 | ByteRange | IsNil | IsPair | Head | Rest | IsNumber | IsSymbol | Spelling.
Inductive expr := Lit (v : value) | Fail (message : string) | Var (i : nat)
 | If (c a b : expr) | Let (a b : expr)
 | Op (p : operation) (a b : expr) | Call (f : function) (a b : expr).
Definition dummy := Lit (Number 0).
Definition unary p a := Op p a dummy.
Definition text s := Lit (Text s).
Definition body f := match f with
 | Byte => If (unary Zero (Var 1)) (text "")
     (Let (unary Half (Var 0))
       (Op Cat (If (Op Even (Var 1) (Var 0)) (text "0") (text "1"))
         (Call Byte (Var 0) (unary Prev (Var 2)))))
 | Str => If (unary Empty (Var 0)) (text "0")
     (Let (unary Code (Var 0))
       (If (unary ByteRange (Var 0))
         (Op Cat (text "1")
           (Op Cat (Call Byte (Var 0) (Lit (Number 8)))
             (Call Str (unary Tail (Var 1)) dummy)))
         (Fail "Wire atoms require byte strings")))
 | Datum => If (unary IsNil (Var 0)) (text "00")
     (If (unary IsPair (Var 0))
       (Op Cat (text "1") (Op Cat (Call Datum (unary Head (Var 0)) dummy)
                                  (Call Datum (unary Rest (Var 0)) dummy)))
       (If (unary IsNumber (Var 0))
         (Op Cat (text "011") (Call Str (unary Spelling (Var 0)) dummy))
         (If (unary IsSymbol (Var 0))
           (Op Cat (text "010") (Call Str (unary Spelling (Var 0)) dummy))
           (Fail "Unsupported wire datum"))))
 end.
Definition primitive p a b : option value := match p,a,b with
 | Cat,Text x,Text y => Some (Text (x ++ y))
 | Zero,Number n,_ => Some (Boolean (Nat.eqb n 0))
 | Half,Number n,_ => Some (Number (Nat.div2 n))
 | Even,Number n,Number half => Some (Boolean (Nat.eqb n (half * 2)))
 | Prev,Number (S n),_ => Some (Number n)
 | Empty,Text s,_ => Some (Boolean (if string_dec s "" then true else false))
 | Code,Text (String c s),_ => Some (Number (nat_of_ascii c))
 | Tail,Text (String c s),_ => Some (Text s)
 | ByteRange,Number n,_ => Some (Boolean (Nat.ltb n 256))
 | IsNil,Data d,_ => Some (Boolean (match d with Wire.Nil => true | _ => false end))
 | IsPair,Data d,_ => Some (Boolean (match d with Wire.Cons _ _ => true | _ => false end))
 | Head,Data (Wire.Cons h t),_ => Some (Data h)
 | Rest,Data (Wire.Cons h t),_ => Some (Data t)
 | IsNumber,Data d,_ => Some (Boolean (match d with Wire.Atom true _ => true | _ => false end))
 | IsSymbol,Data d,_ => Some (Boolean (match d with Wire.Atom false _ => true | _ => false end))
 | Spelling,Data (Wire.Atom tag s),_ => Some (Text s)
 | _,_,_ => None end.
Inductive result := Returned (v : value) | Exhausted | Stuck.
(* Stuck describes explicit errors and undefined primitive/binding cases.
   It is distinct from a fuel limit and is not an evidence rejection verdict. *)
Fixpoint eval fuel (env : list value) e : result := match fuel with
 | 0 => Exhausted
 | S n => match e with
   | Lit v => Returned v | Fail _ => Stuck
   | Var i => match nth_error env i with Some v => Returned v | None => Stuck end
   | If c a b => match eval n env c with
       | Returned (Boolean true) => eval n env a
       | Returned (Boolean false) => eval n env b
       | Exhausted => Exhausted | _ => Stuck end
   | Let a b => match eval n env a with
       | Returned v => eval n (v::env) b | Exhausted => Exhausted | _ => Stuck end
   | Op p a b => match eval n env a with
       | Returned x => match eval n env b with
           | Returned y => match primitive p x y with Some v => Returned v | None => Stuck end
           | Exhausted => Exhausted | _ => Stuck end
       | Exhausted => Exhausted | _ => Stuck end
   | Call f a b => match eval n env a with
       | Returned x => match eval n env b with
           | Returned y => eval n [x;y] (body f)
           | Exhausted => Exhausted | _ => Stuck end
       | Exhausted => Exhausted | _ => Stuck end
   end end.
Lemma eval_monotone : forall n env e v, eval n env e = Returned v ->
 forall m, n <= m -> eval m env e = Returned v.
Proof.
 induction n as [|n IH]; intros env e v H m Hle; [discriminate|].
 destruct m as [|m]; [lia|]. destruct e; cbn [eval] in *; try assumption.
 - destruct (eval n env e1) as [x| |] eqn:E; try discriminate.
   rewrite (IH _ _ _ E m) by lia. destruct x; try discriminate.
   destruct b; eapply IH; eauto; lia.
 - destruct (eval n env e1) as [x| |] eqn:E; try discriminate.
   rewrite (IH _ _ _ E m) by lia. eapply IH; eauto; lia.
 - destruct (eval n env e1) as [x| |] eqn:E; try discriminate.
   destruct (eval n env e2) as [y| |] eqn:F; try discriminate.
   rewrite (IH _ _ _ E m), (IH _ _ _ F m); auto; lia.
 - destruct (eval n env e1) as [x| |] eqn:E; try discriminate.
   destruct (eval n env e2) as [y| |] eqn:F; try discriminate.
   rewrite (IH _ _ _ E m), (IH _ _ _ F m); try lia. eapply IH; eauto; lia.
Qed.
Definition evaluates env e v := exists n, eval n env e = Returned v.
Lemma lit_evaluates : forall env v, evaluates env (Lit v) v.
Proof. intros; exists 1; reflexivity. Qed.
Lemma var_evaluates : forall env i v, nth_error env i = Some v -> evaluates env (Var i) v.
Proof. intros; exists 1; cbn [eval]; rewrite H; reflexivity. Qed.
Lemma op_evaluates : forall env p a b x y v,
 evaluates env a x -> evaluates env b y -> primitive p x y = Some v -> evaluates env (Op p a b) v.
Proof.
 intros env p a b x y v [n H] [m J] K. exists (S (n+m)). cbn [eval].
 rewrite (eval_monotone _ _ _ _ H (n+m)), (eval_monotone _ _ _ _ J (n+m)); try lia. rewrite K; reflexivity.
Qed.
Lemma if_evaluates : forall env c a b flag v,
 evaluates env c (Boolean flag) -> evaluates env (if flag then a else b) v -> evaluates env (If c a b) v.
Proof.
 intros env c a b flag v [n H] [m J]. exists (S (n+m)). cbn [eval].
 rewrite (eval_monotone _ _ _ _ H (n+m)) by lia.
 destruct flag; eapply eval_monotone; eauto; lia.
Qed.
Lemma let_evaluates : forall env a b x v,
 evaluates env a x -> evaluates (x::env) b v -> evaluates env (Let a b) v.
Proof.
 intros env a b x v [n H] [m J]. exists (S (n+m)). cbn [eval].
 rewrite (eval_monotone _ _ _ _ H (n+m)) by lia. eapply eval_monotone; eauto; lia.
Qed.
Lemma call_evaluates : forall env f a b x y v,
 evaluates env a x -> evaluates env b y -> evaluates [x;y] (body f) v -> evaluates env (Call f a b) v.
Proof.
 intros env f a b x y v [n H] [m J] [k K]. exists (S (n+m+k)). cbn [eval].
 rewrite (eval_monotone _ _ _ _ H (n+m+k)), (eval_monotone _ _ _ _ J (n+m+k)); try lia.
 eapply eval_monotone; eauto; lia.
Qed.
Theorem evaluation_deterministic : forall env e x y,
 evaluates env e x -> evaluates env e y -> x = y.
Proof.
 intros env e x y [n H] [m J].
 pose proof (eval_monotone _ _ _ _ H (n+m) ltac:(lia)).
 pose proof (eval_monotone _ _ _ _ J (n+m) ltac:(lia)). congruence.
Qed.
Fixpoint byte_bits n count := match count with
 | 0 => [] | S k => negb (Nat.eqb n (Nat.div2 n * 2)) :: byte_bits (Nat.div2 n) k end.
Ltac leaf := lazymatch goal with
 | |- evaluates _ (Var _) _ => apply var_evaluates; reflexivity
 | _ => apply lit_evaluates end.
Ltac prim := eapply op_evaluates; [leaf | leaf | reflexivity].
Theorem byte_correct : forall count n,
 evaluates [Number n;Number count] (body Byte) (Text (Wire.bit_text (byte_bits n count))).
Proof.
 induction count as [|count IH]; intros n; cbn [body].
 - eapply if_evaluates with (flag:=true); [prim | leaf].
 - eapply if_evaluates with (flag:=false); [prim |].
   eapply let_evaluates; [prim |].
   eapply op_evaluates with (x:=Text (if Nat.eqb n (Nat.div2 n * 2) then "0" else "1")).
   + eapply if_evaluates with (flag:=Nat.eqb n (Nat.div2 n * 2)); [prim |].
     destruct (Nat.eqb n (Nat.div2 n * 2)); leaf.
   + eapply call_evaluates; [leaf | prim | apply IH].
   + cbn [primitive byte_bits Wire.bit_text]. destruct (Nat.eqb n (Nat.div2 n * 2)); reflexivity.
Qed.
Lemma byte_ascii : forall c, byte_bits (nat_of_ascii c) 8 = Wire.char_bits c.
Proof.
 intros [a b c d e f g h]. destruct a,b,c,d,e,f,g,h; reflexivity.
Qed.
Lemma bit_text_app : forall a b, Wire.bit_text (a ++ b) = Wire.bit_text a ++ Wire.bit_text b.
Proof. induction a; intros; simpl; auto. rewrite IHa; reflexivity. Qed.
Theorem string_correct : forall s,
 evaluates [Text s;Number 0] (body Str) (Text (Wire.bit_text (Wire.string_bits s))).
Proof.
 induction s as [|c s IH]; cbn [body].
 - eapply if_evaluates with (flag:=true); [prim | leaf].
 - eapply if_evaluates with (flag:=false); [prim |].
   eapply let_evaluates; [prim |].
   eapply if_evaluates with (flag:=true).
   + eapply op_evaluates; [leaf | leaf |].
     cbn [primitive]. rewrite (proj2 (Nat.ltb_lt _ _) (nat_ascii_bounded c)). reflexivity.
   + eapply op_evaluates; [leaf | |].
     * eapply op_evaluates.
       -- eapply call_evaluates; [leaf | leaf | apply byte_correct].
       -- eapply call_evaluates; [prim | leaf | exact IH].
       -- cbn [primitive]. reflexivity.
     * cbn [primitive Wire.string_bits Wire.bit_text]. rewrite byte_ascii, bit_text_app. reflexivity.
Qed.
Theorem datum_correct : forall d,
 evaluates [Data d;Number 0] (body Datum) (Text (Wire.capture d)).
Proof.
 induction d as [|tag s|a IHa b IHb]; cbn [body].
 - eapply if_evaluates with (flag:=true); [prim | leaf].
 - eapply if_evaluates with (flag:=false); [prim |].
   eapply if_evaluates with (flag:=false); [prim |].
   destruct tag.
   + eapply if_evaluates with (flag:=true); [prim |].
     eapply op_evaluates with (y:=Text (Wire.bit_text (Wire.string_bits s))); [leaf | | reflexivity].
     eapply call_evaluates; [prim | leaf | apply string_correct].
   + eapply if_evaluates with (flag:=false); [prim |].
     eapply if_evaluates with (flag:=true); [prim |].
     eapply op_evaluates with (y:=Text (Wire.bit_text (Wire.string_bits s))); [leaf | | reflexivity].
     eapply call_evaluates; [prim | leaf | apply string_correct].
 - eapply if_evaluates with (flag:=false); [prim |].
   eapply if_evaluates with (flag:=true); [prim |].
   eapply op_evaluates; [leaf | |].
   + eapply op_evaluates.
     * eapply call_evaluates; [prim | leaf | exact IHa].
     * eapply call_evaluates; [prim | leaf | exact IHb].
     * cbn [primitive]. reflexivity.
   + unfold Wire.capture; cbn [Wire.encode Wire.bit_text primitive]. rewrite bit_text_app. reflexivity.
Qed.
Theorem encoder_output_unique : forall d v,
 evaluates [Data d;Number 0] (body Datum) v -> v = Text (Wire.capture d).
Proof. intros; eapply evaluation_deterministic; [eassumption | apply datum_correct]. Qed.
Theorem encoder_decodes : forall d out,
 evaluates [Data d;Number 0] (body Datum) (Text out) -> Wire.decode_text out = Some d.
Proof. intros; apply encoder_output_unique in H. inversion H; apply Wire.capture_roundtrip. Qed.
(* Canonical source for this closed program. The source-link gate checks the
   actual loaded file against this renderer inside Rocq. Only 0, 8 and binary
   text literals occur in these bodies. Unsupported printer cases are marked. *)
Definition function_name f := match f with
 | Byte => "buri.wire-byte" | Str => "buri.wire-string" | Datum => "buri.wire" end.
Definition par1 name a := "(" ++ name ++ " " ++ a ++ ")".
Definition par2 name a b := "(" ++ name ++ " " ++ a ++ " " ++ b ++ ")".
Definition render_op p a b := match p with
 | Cat => par2 "cn" a b | Zero => par2 "=" a "0"
 | Half => par1 "floor" (par2 "/" a "2")
 | Even => par2 "=" a (par2 "*" b "2") | Prev => par2 "-" a "1"
 | Empty => par2 "=" a """""" | Code => par1 "string->n" (par2 "pos" a "0")
 | Tail => par1 "tlstr" a | ByteRange => par2 "and" (par2 ">=" a "0") (par2 "<" a "256")
 | IsNil => par2 "=" a "[]" | IsPair => par1 "cons?" a
 | Head => par1 "hd" a | Rest => par1 "tl" a
 | IsNumber => par1 "buri.exact-integer?" a | IsSymbol => par1 "symbol?" a
 | Spelling => par1 "str" a end.
Fixpoint render names e := match e with
 | Fail message => par1 "simple-error" ("""" ++ message ++ """")
 | Lit (Text s) => """" ++ s ++ """"
 | Lit (Number n) => if Nat.eqb n 0 then "0" else if Nat.eqb n 8 then "8" else "UNSUPPORTED_NUMBER"
 | Lit _ => "UNSUPPORTED_LITERAL"
 | Var i => nth i names "UNBOUND"
 | If c a b => "(if " ++ render names c ++ " " ++ render names a ++ " " ++ render names b ++ ")"
 | Let a b => "(let Local " ++ render names a ++ " " ++ render ("Local"::names) b ++ ")"
 | Op p a b => render_op p (render names a) (render names b)
 | Call f a b => match f with
     | Byte => par2 (function_name f) (render names a) (render names b)
     | _ => par1 (function_name f) (render names a) end
 end.
Definition parameters f := match f with Byte => ["N";"Count"] | Str => ["S"] | Datum => ["X"] end.
Definition render_definition f := "(define " ++ function_name f ++ " " ++
 match f with
 | Byte => "N Count -> " ++ render (parameters f) (body f) ++ ")"
 | Str => "S -> " ++ render (parameters f) (body f) ++ ")"
 | Datum => "X -> " ++ render (parameters f) (body f) ++ ")" end.
Definition newline := String (ascii_of_nat 10) "".
Definition source := "(tc -)" ++ newline ++ render_definition Byte ++ newline ++
 render_definition Str ++ newline ++ render_definition Datum ++ newline.
End Encoder.
