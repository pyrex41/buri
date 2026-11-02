(* E2E-17, Shen-CL wrappers: body proofs of the ACTUAL pinned definitions in
   Shen-CL 4844072d src/primitives.lsp (blob f9b11c8a): the Boolean wrappers
   cons?, string?, number?, shen-cl.equal? and the four comparisons, the
   structural equality shen-cl.absequal, and the integer arithmetic wrappers
   shen-cl.add/subtract/multiply/divide with shen-cl.double-precision.
   The bytes are packaged in PrimitiveSources.v, read by PortReader in CL mode
   and admitted by computed equality with the reviewed expected AST below.
   Two models are used and kept apart:
   - CLLowering's relational CL model (state, effects, Boolean errors), in
     which the Boolean wrappers discharge, at the arity the optimizer emits,
     the named fields of CLLowering.primitive_contracts;
   - a small functional CL evaluator [ceval] for the pure helpers, quantified
     over every host table satisfying the individually named SBCL contracts.
   Host operations (EQ, TYPEP, =, +, /, COERCE, ...) remain named contracts
   owned by E2E-21/E2E-24 (docs/PRIMITIVES.md). cf-vectors is captured but
   not admitted for evaluation: its LOOP body is outside the model and the
   vector branch of absequal is not reached on the data domain proved here. *)
From Coq Require Import String List ZArith Bool Ascii Lia DecimalString DecimalZ DecimalPos.
From Buri Require Import Native PortReader PrimitiveSources Observation KLSyntax KLValue KLSemantics.
From Buri Require CLLowering.
Import ListNotations.
Module CLWrappers.
Module R := PortReader.PortReader.
Open Scope string_scope.
Notation sv := CLLowering.sv.
Notation VSym := CLLowering.VSym.
Notation VStr := CLLowering.VStr.
Notation VNum := CLLowering.VNum.
Notation VNil := CLLowering.VNil.
Notation VCons := CLLowering.VCons.

(* ---------- 1. Decoding and admission ---------- *)
Definition cdef := (list string * list sv)%type.
Definition params_of (v : sv) : option (list string) :=
 match R.to_list v with
 | Some xs => fold_right (fun x acc => match x, acc with VSym s, Some r => Some (s :: r) | _, _ => None end) (Some []) xs
 | None => None end.
Definition defun_of (d : sv) : option (string * cdef) :=
 match R.to_list d with
 | Some (VSym "DEFUN" :: VSym f :: ps :: body) =>
   match params_of ps with Some ps => Some (f, (ps, body)) | None => None end
 | _ => None end.
Definition SL := fold_right VCons VNil.
Definition Sy := VSym.
Definition Q x := SL [Sy "QUOTE"; x].
Definition bool_body g args := SL [Sy "IF"; SL (Sy g :: map Sy args); Q (Sy "true"); Q (Sy "false")].
Definition fx v := SL [Sy "TYPEP"; Sy v; Q (Sy "FIXNUM")].
Definition df v := SL [Sy "TYPEP"; Sy v; Q (Sy "DOUBLE-FLOAT")].
Definition dp v := SL [Sy "shen-cl.double-precision"; Sy v].
Definition absequal_body := SL [Sy "COND";
 SL [SL [Sy "EQ"; Sy "X"; Sy "Y"]; Sy "T"];
 SL [fx "X"; SL [Sy "IF"; fx "Y"; SL [Sy "EQL"; Sy "X"; Sy "Y"];
                 SL [Sy "AND"; SL [Sy "NUMBERP"; Sy "Y"]; SL [Sy "="; Sy "X"; Sy "Y"]]]];
 SL [SL [Sy "NUMBERP"; Sy "X"]; SL [Sy "AND"; SL [Sy "NUMBERP"; Sy "Y"]; SL [Sy "="; Sy "X"; Sy "Y"]]];
 SL [SL [Sy "CONSP"; Sy "X"]; SL [Sy "AND"; SL [Sy "CONSP"; Sy "Y"];
   SL [Sy "shen-cl.absequal"; SL [Sy "CAR"; Sy "X"]; SL [Sy "CAR"; Sy "Y"]];
   SL [Sy "shen-cl.absequal"; SL [Sy "CDR"; Sy "X"]; SL [Sy "CDR"; Sy "Y"]]]];
 SL [SL [Sy "STRINGP"; Sy "X"]; SL [Sy "AND"; SL [Sy "STRINGP"; Sy "Y"]; SL [Sy "STRING="; Sy "X"; Sy "Y"]]];
 SL [SL [Sy "ARRAYP"; Sy "X"]; SL [Sy "AND"; SL [Sy "ARRAYP"; Sy "Y"]; SL [Sy "NOT"; SL [Sy "STRINGP"; Sy "Y"]];
   SL [Sy "CF-VECTORS"; Sy "X"; Sy "Y"; SL [Sy "LENGTH"; Sy "X"]; SL [Sy "LENGTH"; Sy "Y"]]]];
 SL [SL [Sy "SYMBOLP"; Sy "X"]; VNil];
 SL [Sy "T"; SL [Sy "EQUAL"; Sy "X"; Sy "Y"]]].
Definition numeric_equal_body := SL [Sy "IF"; SL [Sy "AND"; SL [Sy "INTEGERP"; Sy "X"]; SL [Sy "INTEGERP"; Sy "Y"]];
 SL [Sy "="; Sy "X"; Sy "Y"];
 SL [Sy "AND"; SL [Sy "NUMBERP"; Sy "X"]; SL [Sy "NUMBERP"; Sy "Y"]; SL [Sy "="; Sy "X"; Sy "Y"]]].
Definition double_precision_body := SL [Sy "IF"; SL [Sy "TYPEP"; Sy "X"; Q (SL [Sy "OR"; Sy "INTEGER"; Sy "DOUBLE-FLOAT"])];
 Sy "X"; SL [Sy "COERCE"; Sy "X"; Q (Sy "DOUBLE-FLOAT")]].
Definition xy g := SL [Sy g; Sy "X"; Sy "Y"].
Definition multiply_body := SL [Sy "COND";
 SL [SL [Sy "AND"; fx "X"; fx "Y"]; xy "*"];
 SL [SL [Sy "AND"; df "X"; df "Y"]; SL [Sy "IF"; SL [Sy "OR"; SL [Sy "ZEROP"; Sy "X"]; SL [Sy "ZEROP"; Sy "Y"]]; VNum "0"; xy "*"]];
 SL [SL [Sy "OR"; SL [Sy "ZEROP"; Sy "X"]; SL [Sy "ZEROP"; Sy "Y"]]; VNum "0"];
 SL [Sy "T"; SL [Sy "*"; dp "X"; dp "Y"]]].
Definition additive_body g := SL [Sy "COND";
 SL [SL [Sy "AND"; fx "X"; fx "Y"]; xy g];
 SL [SL [Sy "AND"; df "X"; df "Y"]; xy g];
 SL [Sy "T"; SL [Sy g; dp "X"; dp "Y"]]].
Definition divide_body := SL [Sy "LET"; SL [SL [Sy "DIV"; SL [Sy "/"; dp "X"; dp "Y"]]];
 SL [Sy "IF"; SL [Sy "INTEGERP"; Sy "DIV"]; Sy "DIV";
     SL [Sy "*"; SL [Sy "COERCE"; VNum "1.0"; Q (Sy "DOUBLE-FLOAT")]; Sy "DIV"]]].
(* (if (typep x 'fixnum) (1+ (the fixnum x)) (1+ x)), and 1- for decrement. *)
Definition step_body g := SL [Sy "IF"; fx "X"; SL [Sy g; SL [Sy "THE"; Sy "FIXNUM"; Sy "X"]]; SL [Sy g; Sy "X"]].
Definition expected_program : list (string * cdef) := [
 ("cons?", (["X"], [bool_body "CONSP" ["X"]]));
 ("string?", (["S"], [bool_body "STRINGP" ["S"]]));
 ("number?", (["N"], [bool_body "NUMBERP" ["N"]]));
 ("shen-cl.equal?", (["X"; "Y"], [bool_body "shen-cl.absequal" ["X"; "Y"]]));
 ("shen-cl.absequal", (["X"; "Y"], [absequal_body]));
 ("shen-cl.numeric-equal", (["X"; "Y"], [numeric_equal_body]));
 ("shen-cl.double-precision", (["X"], [double_precision_body]));
 ("shen-cl.multiply", (["X"; "Y"], [multiply_body]));
 ("shen-cl.add", (["X"; "Y"], [additive_body "+"]));
 ("shen-cl.subtract", (["X"; "Y"], [additive_body "-"]));
 ("shen-cl.divide", (["X"; "Y"], [divide_body]));
 ("shen-cl.greater?", (["X"; "Y"], [bool_body ">" ["X"; "Y"]]));
 ("shen-cl.less?", (["X"; "Y"], [bool_body "<" ["X"; "Y"]]));
 ("shen-cl.greater-than-or-equal-to?", (["X"; "Y"], [bool_body ">=" ["X"; "Y"]]));
 ("shen-cl.less-than-or-equal-to?", (["X"; "Y"], [bool_body "<=" ["X"; "Y"]]));
 ("shen-cl.increment", (["X"], [step_body "1+"]));
 ("shen-cl.decrement", (["X"], [step_body "1-"]))].

Fixpoint decode_all (ds : list sv) : option (list (string * cdef)) := match ds with
 | [] => Some []
 | d :: ds => match defun_of d, decode_all ds with Some x, Some r => Some (x :: r) | _, _ => None end end.
Fixpoint lbeq {A} (f : A -> A -> bool) (xs ys : list A) : bool := match xs, ys with
 | [], [] => true | x :: xs, y :: ys => (f x y && lbeq f xs ys)%bool | _, _ => false end.
Definition cdef_eqb (a b : string * cdef) :=
 (String.eqb (fst a) (fst b) && lbeq String.eqb (fst (snd a)) (fst (snd b))
  && lbeq CLLowering.sv_eqb (snd (snd a)) (snd (snd b)))%bool.
(* cf-vectors (seventh form) is read and identified, never admitted for evaluation. *)
Definition admission_of (src : string) : option (list (string * cdef)) :=
 match R.read true src with
 | Some (a :: b :: c :: d :: e :: f :: cf :: rest) =>
   match defun_of cf, decode_all (a :: b :: c :: d :: e :: f :: rest) with
   | Some ("CF-VECTORS", (["X"; "Y"; "LX"; "LY"], _)), Some ds =>
     if lbeq cdef_eqb ds expected_program then Some ds else None
   | _, _ => None end
 | _ => None end.
Definition admission := admission_of cl_source.
Theorem cl_wrappers_admitted : admission = Some expected_program.
Proof. vm_compute. reflexivity. Qed.
Definition program := expected_program.
Fixpoint assoc (f : string) (l : list (string * cdef)) : option cdef := match l with
 | [] => None | (g, d) :: r => if String.eqb f g then Some d else assoc f r end.

(* ---------- 2. Boolean wrappers in CLLowering's relational CL model ---------- *)
Section Relational.
Variable St : Type.
Variable hp : string -> list sv -> St -> CLLowering.out St -> Prop.
Variable other : CLLowering.binding -> sv -> St -> CLLowering.out St -> Prop.
(* The world whose primitive relation runs the captured wrapper bodies over
   the host relation [hp]. A call with the wrong number of arguments is given
   no meaning (SBCL signals a program-error with a fresh condition object). *)
Definition boolean_wrappers := ["cons?"; "string?"; "number?"; "shen-cl.equal?"; "shen-cl.greater?";
 "shen-cl.less?"; "shen-cl.greater-than-or-equal-to?"; "shen-cl.less-than-or-equal-to?"].
Definition is_wrapper f := existsb (String.eqb f) boolean_wrappers.
Definition wrapped (f : string) (vs : list sv) (s : St) (o : CLLowering.out St) : Prop :=
 match is_wrapper f, assoc f program with
 | true, Some (ps, [b]) => List.length ps = List.length vs /\ CLLowering.ev St hp other (combine ps vs) b s o
 | _, _ => hp f vs s o end.
Lemma var_pure : forall e x v, x <> "T" -> CLLowering.lookup x e = Some v ->
 forall s o, CLLowering.ev St hp other e (VSym x) s o <-> o = CLLowering.Ok v s.
Proof.
 intros e x v Nt Hl s o. split; intro H.
 - inversion H; subst; congruence.
 - subst. apply CLLowering.ev_lex; auto.
Qed.
Lemma host_call : forall g e xs vs s t, CLLowering.is_fn g = true -> g <> CLLowering.TRUEP ->
 (forall o s', CLLowering.ev_list St hp other e (SL (map Sy xs)) s' o <-> o = CLLowering.LOkL St vs s') ->
 CLLowering.CLT St hp other e (VCons (VSym g) (SL (map Sy xs))) s t <-> exists o, hp g vs s o /\ CLLowering.cl_test St o = t.
Proof.
 intros g e xs vs s t Hf Ng Hl. unfold CLLowering.CLT. rewrite (CLLowering.obs_call St hp other) by exact Hf.
 split.
 - intros [[ws [s1 [o [L [A T]]]]]|[o [L T]]].
   + apply Hl in L. injection L as -> ->. apply (CLLowering.apply_fn_prim St hp) in A; auto. eauto.
   + apply Hl in L. discriminate.
 - intros [o [H T]]. left. exists vs, s, o. repeat split; auto. apply Hl; reflexivity.
   apply (CLLowering.apply_fn_prim St hp); auto.
Qed.
Lemma list_vars1 : forall x v s' o, x <> "T" ->
 CLLowering.ev_list St hp other [(x, v)] (SL (map Sy [x])) s' o <-> o = CLLowering.LOkL St [v] s'.
Proof.
 intros x v s' o Nt. cbn [map SL fold_right]. rewrite CLLowering.list1_iff. split.
 - intros [[w [s1 [H ->]]]|[o' [H [A ->]]]]; apply (var_pure [(x, v)] x v Nt) in H; cbn; try (rewrite String.eqb_refl; reflexivity).
   + injection H as -> ->; reflexivity.
   + subst; contradiction.
 - intros ->. left. exists v, s'. split; auto. apply (var_pure [(x, v)] x v Nt); [cbn; rewrite String.eqb_refl; reflexivity|reflexivity].
Qed.
Lemma list_vars2 : forall v w s' o,
 CLLowering.ev_list St hp other [("X", v); ("Y", w)] (SL (map Sy ["X"; "Y"])) s' o <-> o = CLLowering.LOkL St [v; w] s'.
Proof.
 intros v w s' o. cbn [map SL fold_right]. rewrite CLLowering.list2_iff.
 assert (HX : forall s o, CLLowering.ev St hp other [("X", v); ("Y", w)] (VSym "X") s o <-> o = CLLowering.Ok v s)
   by (apply var_pure; [discriminate|reflexivity]).
 assert (HY : forall s o, CLLowering.ev St hp other [("X", v); ("Y", w)] (VSym "Y") s o <-> o = CLLowering.Ok w s)
   by (apply var_pure; [discriminate|reflexivity]).
 split.
 - intros [[a [s1 [b [s2 [Ha [Hb ->]]]]]]|[[o' [Ha [A ->]]]|[a [s1 [o' [Ha [Hb [A ->]]]]]]]].
   + apply HX in Ha; apply HY in Hb. injection Ha as -> ->; injection Hb as -> ->. reflexivity.
   + apply HX in Ha; subst; contradiction.
   + apply HY in Hb; subst; contradiction.
 - intros ->. left. exists v, s', w, s'. split; [apply HX|split; [apply HY|]]; reflexivity.
Qed.
(* Every captured Boolean wrapper (IF (g X..) 'true 'false), in test position
   under Shen truth, is observationally the CL test of the host predicate g. *)
Lemma wrapper_test : forall f g xs vs, assoc f program = Some (xs, [bool_body g xs]) ->
 List.length xs = List.length vs -> CLLowering.is_fn g = true -> g <> CLLowering.TRUEP -> is_wrapper f = true -> is_wrapper g = false ->
 (forall o s', CLLowering.ev_list St hp other (combine xs vs) (SL (map Sy xs)) s' o <-> o = CLLowering.LOkL St vs s') ->
 CLLowering.args_refine St wrapped f vs g vs.
Proof.
 intros f g xs vs Ha Hlen Hf Ng Wf Wg Hl s t. unfold wrapped at 1 2. rewrite Wf, Ha, Wg.
 transitivity (CLLowering.SHT St hp other (combine xs vs) (bool_body g xs) s t).
 - unfold CLLowering.SHT, CLLowering.Obs. split; intros [o [H T]]; exists o; [destruct H|]; auto.
 - transitivity (CLLowering.CLT St hp other (combine xs vs) (VCons (VSym g) (SL (map Sy xs))) s t);
   [apply (CLLowering.sem_if_tf St hp other) | apply host_call; auto].
Qed.
Theorem cons_wrapper : forall v, CLLowering.args_refine St wrapped "cons?" [v] "CONSP" [v].
Proof. intro v. apply (wrapper_test _ _ ["X"]); try reflexivity; try discriminate. intros; apply list_vars1; discriminate. Qed.
Theorem string_wrapper : forall v, CLLowering.args_refine St wrapped "string?" [v] "STRINGP" [v].
Proof. intro v. apply (wrapper_test _ _ ["S"]); try reflexivity; try discriminate. intros; apply list_vars1; discriminate. Qed.
Theorem number_wrapper : forall v, CLLowering.args_refine St wrapped "number?" [v] "NUMBERP" [v].
Proof. intro v. apply (wrapper_test _ _ ["N"]); try reflexivity; try discriminate. intros; apply list_vars1; discriminate. Qed.
Theorem equal_wrapper : forall v w, CLLowering.args_refine St wrapped CLLowering.EQUALP [v; w] "shen-cl.absequal" [v; w].
Proof. intros v w. apply (wrapper_test _ _ ["X"; "Y"]); try reflexivity; try discriminate. intros; apply list_vars2. Qed.
Theorem comparison_wrappers : forall v w,
 CLLowering.args_refine St wrapped "shen-cl.greater?" [v; w] ">" [v; w] /\
 CLLowering.args_refine St wrapped "shen-cl.greater-than-or-equal-to?" [v; w] ">=" [v; w] /\
 CLLowering.args_refine St wrapped "shen-cl.less?" [v; w] "<" [v; w] /\
 CLLowering.args_refine St wrapped "shen-cl.less-than-or-equal-to?" [v; w] "<=" [v; w].
Proof.
 intros v w. repeat split; apply (wrapper_test _ _ ["X"; "Y"]); try reflexivity; try discriminate; intros; apply list_vars2.
Qed.
End Relational.

(* ---------- 3. A functional evaluator for the pure helpers ---------- *)
Inductive cres := CRet (v : sv) | CRaise (x : sv) | CFuel | CUnsup.
Definition T := VSym "T".
Definition hb (b : bool) := if b then T else VNil.
Definition truthy (v : sv) := match v with VNil => false | _ => true end.
Definition special h := existsb (String.eqb h)
 ["DECLARE"; "LOOP"; "THE"; "FUNCTION"; "SETQ"; "SETF"; "LAMBDA"; "DEFUN"; "LET*"; "PROGN"; "BLOCK"; "RETURN"; "TAGBODY"; "GO"].
Fixpoint ceval (n : nat) (h : string -> list sv -> cres) (env : CLLowering.binding) (e : sv) {struct n} : cres :=
 match n with
 | O => CFuel
 | S m =>
   let args := fix args (xs : list sv) : list sv + cres := match xs with
     | [] => inl []
     | x :: r => match ceval m h env x with
       | CRet v => match args r with inl vs => inl (v :: vs) | inr o => inr o end
       | o => inr o end end in
   match e with
   | VNil => CRet VNil
   | VSym x => if String.eqb x "T" then CRet T
     else match CLLowering.lookup x env with Some v => CRet v | None => CUnsup end
   | VStr _ | VNum _ | CLLowering.VObj _ => CRet e
   | VCons (VSym hd) rest => match R.to_list rest with
     | None => CUnsup
     | Some xs =>
       if String.eqb hd "QUOTE" then match xs with [d] => CRet d | _ => CUnsup end
       else if String.eqb hd "IF" then match xs with
         | [c; a; b] => match ceval m h env c with CRet v => if truthy v then ceval m h env a else ceval m h env b | o => o end
         | _ => CUnsup end
       else if String.eqb hd "COND" then
         (fix clauses cs := match cs with
          | [] => CRet VNil
          | cl :: cs => match R.to_list cl with
            | Some [t; b] => match ceval m h env t with CRet v => if truthy v then ceval m h env b else clauses cs | o => o end
            | _ => CUnsup end end) xs
       else if String.eqb hd "AND" then
         (fix ands xs := match xs with
          | [] => CRet T | [x] => ceval m h env x
          | x :: r => match ceval m h env x with CRet VNil => CRet VNil | CRet _ => ands r | o => o end end) xs
       else if String.eqb hd "OR" then
         (fix ors xs := match xs with
          | [] => CRet VNil | [x] => ceval m h env x
          | x :: r => match ceval m h env x with CRet VNil => ors r | CRet v => CRet v | o => o end end) xs
       else if String.eqb hd "LET" then match xs with
         | [bs; body] => match R.to_list bs with
           | Some [b] => match R.to_list b with
             | Some [VSym x; init] => match ceval m h env init with CRet v => ceval m h ((x, v) :: env) body | o => o end
             | _ => CUnsup end
           | _ => CUnsup end
         | _ => CUnsup end
       (* (THE type x) evaluates x; the type declaration is not checked
          (SBCL's checking of it is a host contract, cl_step_ops). *)
       else if String.eqb hd "THE" then match xs with [_; x] => ceval m h env x | _ => CUnsup end
       else if special hd then CUnsup
       else match args xs with
         | inr o => o
         | inl vs => match assoc hd program with
           | Some (ps, [body]) => if Nat.eqb (List.length ps) (List.length vs) then ceval m h (combine ps vs) body else CUnsup
           | Some _ => CUnsup
           | None => h hd vs end end end
   | _ => CUnsup end end.

Lemma to_list_SL : forall l, R.to_list (SL l) = Some l.
Proof. induction l; cbn; [reflexivity|]. change (fold_right VCons VNil l) with (SL l). rewrite IHl; reflexivity. Qed.
Section Steps.
Variable h : string -> list sv -> cres.
Lemma ce_var : forall m env x v, String.eqb x "T" = false -> CLLowering.lookup x env = Some v -> ceval (S m) h env (VSym x) = CRet v.
Proof. intros; cbn; rewrite ?to_list_SL; cbn; rewrite H, H0; reflexivity. Qed.
Lemma ce_if : forall m env c a b v, ceval m h env c = CRet v ->
 ceval (S m) h env (SL [Sy "IF"; c; a; b]) = if truthy v then ceval m h env a else ceval m h env b.
Proof. intros; cbn; rewrite ?to_list_SL; cbn; rewrite H; reflexivity. Qed.
Lemma ce_cond_hit : forall m env t b cs v, ceval m h env t = CRet v -> truthy v = true ->
 ceval (S m) h env (SL (Sy "COND" :: SL [t; b] :: cs)) = ceval m h env b.
Proof. intros; cbn; rewrite ?to_list_SL; cbn; rewrite H, H0; reflexivity. Qed.
Lemma ce_cond_miss : forall m env t b cs, ceval m h env t = CRet VNil ->
 ceval (S m) h env (SL (Sy "COND" :: SL [t; b] :: cs)) = ceval (S m) h env (SL (Sy "COND" :: cs)).
Proof. intros; cbn; rewrite ?to_list_SL; cbn; rewrite H; reflexivity. Qed.
Lemma ce_and2 : forall m env x y v, ceval m h env x = CRet v ->
 ceval (S m) h env (SL [Sy "AND"; x; y]) = if truthy v then ceval m h env y else CRet VNil.
Proof. intros; cbn; rewrite H; destruct v; reflexivity. Qed.
Lemma ce_and3 : forall m env x y z v, ceval m h env x = CRet v ->
 ceval (S m) h env (SL [Sy "AND"; x; y; z]) = if truthy v then ceval (S m) h env (SL [Sy "AND"; y; z]) else CRet VNil.
Proof. intros; cbn; rewrite H; destruct v; reflexivity. Qed.
Lemma ce_or2 : forall m env x y v, ceval m h env x = CRet v ->
 ceval (S m) h env (SL [Sy "OR"; x; y]) = if truthy v then CRet v else ceval m h env y.
Proof. intros; cbn; rewrite H; destruct v; reflexivity. Qed.
Lemma ce_quote : forall m env d, ceval (S m) h env (Q d) = CRet d.
Proof. reflexivity. Qed.
Definition plain g := negb (String.eqb g "QUOTE" || String.eqb g "IF" || String.eqb g "COND" || String.eqb g "AND"
 || String.eqb g "OR" || String.eqb g "LET" || String.eqb g "THE" || special g)%bool.
Lemma plain_split : forall g, plain g = true -> String.eqb g "QUOTE" = false /\ String.eqb g "IF" = false /\
 String.eqb g "COND" = false /\ String.eqb g "AND" = false /\ String.eqb g "OR" = false /\ String.eqb g "LET" = false /\
 String.eqb g "THE" = false /\ special g = false.
Proof.
 intros g H. unfold plain in H. apply Bool.negb_true_iff in H.
 repeat (apply Bool.orb_false_iff in H as [H ?]). repeat split; assumption.
Qed.
Ltac plain_rw P := let Q := fresh in pose proof (plain_split _ P) as Q;
 destruct Q as [Q1 [Q2 [Q3 [Q4 [Q5 [Q6 [Q8 Q7]]]]]]];
 cbn [ceval R.to_list SL fold_right option_map Sy]; rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q8, Q7.
Lemma ce_host1 : forall m env g x v r, plain g = true -> assoc g program = None ->
 ceval m h env x = CRet v -> h g [v] = r -> ceval (S m) h env (SL [Sy g; x]) = r.
Proof. intros m env g x v r P A Hx Hr. plain_rw P. rewrite Hx, A. exact Hr. Qed.
Lemma ce_host2 : forall m env g x y v w r, plain g = true -> assoc g program = None ->
 ceval m h env x = CRet v -> ceval m h env y = CRet w -> h g [v; w] = r -> ceval (S m) h env (SL [Sy g; x; y]) = r.
Proof. intros m env g x y v w r P A Hx Hy Hr. plain_rw P. rewrite Hx, Hy, A. exact Hr. Qed.
Lemma ce_def2 : forall m env g x y v w ps body, plain g = true -> assoc g program = Some (ps, [body]) -> List.length ps = 2 ->
 ceval m h env x = CRet v -> ceval m h env y = CRet w ->
 ceval (S m) h env (SL [Sy g; x; y]) = ceval m h (combine ps [v; w]) body.
Proof. intros m env g x y v w ps body P A L Hx Hy. plain_rw P. rewrite Hx, Hy, A, L. reflexivity. Qed.
Lemma ce_def1 : forall m env g x v ps body, plain g = true -> assoc g program = Some (ps, [body]) -> List.length ps = 1 ->
 ceval m h env x = CRet v -> ceval (S m) h env (SL [Sy g; x]) = ceval m h (combine ps [v]) body.
Proof. intros m env g x v ps body P A L Hx. plain_rw P. rewrite Hx, A, L. reflexivity. Qed.
End Steps.
Ltac host := first [eapply ce_host2; [reflexivity|reflexivity| | | ] | eapply ce_host1; [reflexivity|reflexivity| | ]].
Ltac cvar := apply ce_var; reflexivity.

(* ---------- 4. shen-cl.absequal on first-order data ---------- *)
Definition zs (z : Z) := VNum (Native.spelling z).
Inductive cdata : sv -> Prop :=
 | cd_sym s : cdata (VSym s) | cd_str s : cdata (VStr s) | cd_nil : cdata VNil
 | cd_int z : cdata (zs z) | cd_cons a b : cdata a -> cdata b -> cdata (VCons a b).
Definition is_num v := match v with VNum _ => true | _ => false end.
Definition is_cons v := match v with VCons _ _ => true | _ => false end.
Definition is_str v := match v with VStr _ => true | _ => false end.
(* Each SBCL operation reached by absequal on data, named separately. EQ is
   only sound, and complete when either side is a symbol or NIL. *)
Record sbcl_equality_ops (h : string -> list sv -> cres) : Prop := {
 sbcl_eq : forall a b, cdata a -> cdata b -> exists r, h "EQ" [a; b] = CRet (hb r) /\
   (r = true -> a = b) /\ ((CLLowering.symbolic a || CLLowering.symbolic b)%bool = true -> a = b -> r = true);
 sbcl_typep_fixnum : forall a, cdata a -> exists r, h "TYPEP" [a; VSym "FIXNUM"] = CRet (hb r) /\ (r = true -> is_num a = true);
 sbcl_eql_int : forall x y, h "EQL" [zs x; zs y] = CRet (hb (Z.eqb x y));
 sbcl_numberp : forall a, cdata a -> h "NUMBERP" [a] = CRet (hb (is_num a));
 sbcl_num_eq_int : forall x y, h "=" [zs x; zs y] = CRet (hb (Z.eqb x y));
 sbcl_consp : forall a, cdata a -> h "CONSP" [a] = CRet (hb (is_cons a));
 sbcl_car : forall a b, h "CAR" [VCons a b] = CRet a;
 sbcl_cdr : forall a b, h "CDR" [VCons a b] = CRet b;
 sbcl_stringp : forall a, cdata a -> h "STRINGP" [a] = CRet (hb (is_str a));
 sbcl_string_eq : forall s t, h "STRING=" [VStr s; VStr t] = CRet (hb (String.eqb s t));
 sbcl_arrayp : forall a, cdata a -> h "ARRAYP" [a] = CRet (hb (is_str a));
 sbcl_symbolp : forall a, cdata a -> CLLowering.symbolic a = true -> h "SYMBOLP" [a] = CRet T }.
Lemma spelling_inj : forall x y, Native.spelling x = Native.spelling y -> x = y.
Proof.
 assert (G : forall z, NilZero.int_of_string (NilZero.string_of_int (Z.to_int z)) = Some (Z.to_int z)).
 { intro z; apply NilZero.isi; destruct z; cbn; try discriminate; intro E; injection E;
   apply DecimalPos.Unsigned.to_uint_nonnil. }
 intros x y H. apply DecimalZ.to_int_inj. pose proof (G x) as Gx. unfold Native.spelling in H. rewrite H, G in Gx. congruence.
Qed.
Lemma zs_eqb : forall x y, CLLowering.sv_eqb (zs x) (zs y) = Z.eqb x y.
Proof.
 intros x y. cbn. destruct (Z.eqb x y) eqn:E.
 - apply Z.eqb_eq in E; subst; apply String.eqb_refl.
 - apply String.eqb_neq. intro H; apply spelling_inj in H; subst; rewrite Z.eqb_refl in E; discriminate.
Qed.
Fixpoint cbound (v : sv) : nat := match v with VCons a b => 10 + Nat.max (cbound a) (cbound b) | _ => 10 end.
Definition env2 a b : CLLowering.binding := [("X", a); ("Y", b)].
Lemma cdata_num : forall a, cdata a -> is_num a = true -> exists z, a = zs z.
Proof. intros a H; destruct H; cbn; try discriminate; eauto. Qed.
Section Absequal.
Variable h : string -> list sv -> cres.
Hypothesis C : sbcl_equality_ops h.
Lemma numeric_tail : forall m x b, cdata b ->
 ceval (S (S (S m))) h (env2 (zs x) b) (SL [Sy "AND"; SL [Sy "NUMBERP"; Sy "Y"]; SL [Sy "="; Sy "X"; Sy "Y"]]) =
 CRet (hb (CLLowering.sv_eqb (zs x) b)).
Proof.
 intros m x b Db. rewrite (ce_and2 _ _ _ _ _ (hb (is_num b))) by (host; [cvar|apply (sbcl_numberp h C); exact Db]).
 destruct Db as [s|s| |z|a1 a2 D1 D2]; try reflexivity.
 assert (is_num (zs z) = true) as -> by reflexivity. cbn [truthy hb].
 host; [cvar|cvar|]. rewrite (sbcl_num_eq_int h C), zs_eqb. reflexivity.
Qed.
Theorem absequal_data : forall a b n, cdata a -> cdata b -> n >= cbound a ->
 ceval n h (env2 a b) absequal_body = CRet (hb (CLLowering.sv_eqb a b)).
Proof.
 intros a b n Da. revert b n. induction Da as [s|s| |z|a1 a2 D1 IH1 D2 IH2]; intros b n Db Hn;
 (assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); cbn [cbound zs] in Hn; lia));
 unfold absequal_body;
 (match goal with |- context[env2 ?a0 _] => assert (Da0 : cdata a0) by (constructor; auto) end);
 destruct (sbcl_eq h C _ b Da0 Db) as [r [Er [Sound Comp]]];
 (destruct r;
  [ rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|cvar|exact Er]));
    rewrite (Sound eq_refl); cbn; rewrite ?String.eqb_refl, ?(proj2 (CLLowering.sv_eqb_eq _ _) eq_refl); reflexivity
  | rewrite ce_cond_miss by (host; [cvar|cvar|exact Er])]).
 all: destruct (sbcl_typep_fixnum h C _ Da0) as [q [Eq Hq]].
 (* symbol, string, nil, cons: not numbers *)
 1,2,3,5: (destruct q; [specialize (Hq eq_refl); discriminate|]);
   rewrite ce_cond_miss by (host; [cvar|reflexivity|exact Eq]);
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_numberp h C); constructor; auto]).
 - (* symbol *)
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_consp h C); constructor]).
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_stringp h C); constructor]).
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_arrayp h C); constructor]).
   rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|apply (sbcl_symbolp h C); [constructor|reflexivity]])).
   destruct (CLLowering.sv_eqb (VSym s) b) eqn:E; [|reflexivity].
   apply CLLowering.sv_eqb_eq in E. specialize (Comp eq_refl E). discriminate.
 - (* string *)
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_consp h C); constructor]).
   rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|apply (sbcl_stringp h C); constructor])).
   rewrite (ce_and2 _ _ _ _ _ (hb (is_str b))) by (host; [cvar|apply (sbcl_stringp h C); exact Db]).
   destruct b; inversion Db; subst; cbn [truthy hb is_str]; try reflexivity.
   host; [cvar|cvar|apply (sbcl_string_eq h C)].
 - (* nil *)
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_consp h C); constructor]).
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_stringp h C); constructor]).
   rewrite ce_cond_miss by (host; [cvar|apply (sbcl_arrayp h C); constructor]).
   rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|apply (sbcl_symbolp h C); [constructor|reflexivity]])).
   destruct (CLLowering.sv_eqb VNil b) eqn:E; [|reflexivity].
   apply CLLowering.sv_eqb_eq in E. specialize (Comp eq_refl E). discriminate.
 - (* cons *)
   rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|apply (sbcl_consp h C); constructor; auto])).
   rewrite (ce_and3 _ _ _ _ _ _ (hb (is_cons b))) by (host; [cvar|apply (sbcl_consp h C); exact Db]).
   destruct b; inversion Db; subst; cbn [truthy hb is_cons]; try reflexivity.
   cbn [cbound] in Hn.
   rewrite (ce_and2 _ _ _ _ _ (hb (CLLowering.sv_eqb a1 b1))).
   + cbn [CLLowering.sv_eqb]. destruct (CLLowering.sv_eqb a1 b1); cbn [truthy hb andb]; [|reflexivity].
     rewrite (ce_def2 _ _ _ _ _ _ a2 b2 ["X"; "Y"] absequal_body) by (reflexivity || (host; [cvar|apply (sbcl_cdr h C)])).
     apply IH2; auto; lia.
   + rewrite (ce_def2 _ _ _ _ _ _ a1 b1 ["X"; "Y"] absequal_body) by (reflexivity || (host; [cvar|apply (sbcl_car h C)])).
     apply IH1; auto; lia.
 - (* integer *)
   destruct q.
   + rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|reflexivity|exact Eq])).
     destruct (sbcl_typep_fixnum h C _ Db) as [q' [Eq' Hq']].
     rewrite (ce_if _ _ _ _ _ _ (hb q')) by (host; [cvar|reflexivity|exact Eq']).
     destruct q'; cbn [truthy hb].
     * destruct (cdata_num _ Db (Hq' eq_refl)) as [y ->]. host; [cvar|cvar|]. rewrite (sbcl_eql_int h C), zs_eqb. reflexivity.
     * apply numeric_tail; exact Db.
   + rewrite ce_cond_miss by (host; [cvar|reflexivity|exact Eq]).
     rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (host; [cvar|apply (sbcl_numberp h C); constructor])).
     apply numeric_tail; exact Db.
Qed.
(* shen-cl.equal? on data: the Shen Boolean of structural equality. *)
Theorem equal_data : forall a b n, cdata a -> cdata b -> n >= S (S (S (cbound a))) ->
 ceval n h (env2 a b) (bool_body "shen-cl.absequal" ["X"; "Y"]) =
 CRet (VSym (if CLLowering.sv_eqb a b then "true" else "false")).
Proof.
 intros a b n Da Db Hn. assert (exists m, n = S (S (S m))) as [m ->] by (exists (n - 3); lia).
 unfold bool_body. cbn [map].
 rewrite (ce_if _ _ _ _ _ _ (hb (CLLowering.sv_eqb a b))).
 - destruct (CLLowering.sv_eqb a b); reflexivity.
 - rewrite (ce_def2 _ _ _ _ _ _ a b ["X"; "Y"] absequal_body) by (reflexivity || cvar). apply absequal_data; auto; lia.
Qed.
(* The optimizer's EQ rewrite of (shen-cl.equal? X 'D) is exact when D is a
   symbol or NIL: for every data X, EQ answers absequal's answer. *)
Theorem eq_rewrite_safe : forall x d n, cdata x -> cdata d -> CLLowering.symbolic d = true -> n >= cbound x ->
 h "EQ" [x; d] = ceval n h (env2 x d) absequal_body.
Proof.
 intros x d n Dx Dd Sd Hn. rewrite absequal_data by auto.
 destruct (sbcl_eq h C x d Dx Dd) as [r [E [Sound Comp]]]. rewrite E. f_equal.
 destruct r.
 - rewrite (Sound eq_refl), (proj2 (CLLowering.sv_eqb_eq d d) eq_refl). reflexivity.
 - destruct (CLLowering.sv_eqb x d) eqn:Q; [|reflexivity].
   apply CLLowering.sv_eqb_eq in Q. rewrite Comp; auto. rewrite Sd, orb_true_r; reflexivity.
Qed.
End Absequal.

(* A concrete host table satisfying every named contract (anti-vacuity). Its
   EQ identifies only symbols and NIL, as the CL standard permits. *)
Definition model_h (f : string) (vs : list sv) : cres :=
 match f, vs with
 | "EQ", [a; b] => CRet (hb (CLLowering.symbolic a && CLLowering.sv_eqb a b))
 | "TYPEP", [a; VSym "FIXNUM"] => CRet (hb (is_num a))
 | "EQL", [a; b] => CRet (hb (CLLowering.sv_eqb a b))
 | "NUMBERP", [a] => CRet (hb (is_num a))
 | "=", [a; b] => CRet (hb (CLLowering.sv_eqb a b))
 | "CONSP", [a] => CRet (hb (is_cons a))
 | "CAR", [VCons a _] => CRet a
 | "CDR", [VCons _ b] => CRet b
 | "STRINGP", [a] => CRet (hb (is_str a))
 | "STRING=", [VStr s; VStr t] => CRet (hb (String.eqb s t))
 | "ARRAYP", [a] => CRet (hb (is_str a))
 | "SYMBOLP", [a] => CRet (hb (CLLowering.symbolic a))
 | _, _ => CUnsup end.
Theorem model_equality_ops : sbcl_equality_ops model_h.
Proof.
 constructor; intros.
 - exists (CLLowering.symbolic a && CLLowering.sv_eqb a b)%bool. split; [reflexivity|split].
   + intro E. apply andb_true_iff in E as [_ E]. apply CLLowering.sv_eqb_eq; exact E.
   + intros S ->. rewrite orb_diag in S. rewrite S. apply CLLowering.sv_eqb_eq; reflexivity.
 - exists (is_num a). split; auto.
 - exact (f_equal (fun q => CRet (hb q)) (zs_eqb x y)).
 - reflexivity.
 - exact (f_equal (fun q => CRet (hb q)) (zs_eqb x y)).
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - change (CRet (hb (CLLowering.symbolic a)) = CRet T). rewrite H0; reflexivity.
Qed.
(* ... and in that table the rewrite is wrong for every non-symbolic data
   comparand: EQ of D with itself is NIL while absequal answers T. So the
   symbolic restriction (CLLowering.qsafe) is exactly the safe domain at the
   contract level. SBCL itself answers NIL for a fresh equal list, a fresh
   equal string and (EQ 1 1.0d0) (ports/shen-cl-primitive-samples.lisp). *)
Theorem eq_rewrite_unsafe : forall d n, cdata d -> CLLowering.symbolic d = false -> n >= cbound d ->
 model_h "EQ" [d; d] = CRet VNil /\ ceval n model_h (env2 d d) absequal_body = CRet T.
Proof.
 intros d n Dd Sd Hn. split.
 - cbn. rewrite Sd. reflexivity.
 - rewrite (absequal_data model_h model_equality_ops) by auto. rewrite (proj2 (CLLowering.sv_eqb_eq d d) eq_refl). reflexivity.
Qed.

(* ---------- 5. Integer arithmetic wrappers ---------- *)
(* Named SBCL arithmetic contracts on canonical integer spellings. [ratio x y]
   is the host's non-integral exact quotient, [one_d] the double 1.0d0,
   [to_double x y] the double nearest x/y produced by multiplying 1.0d0 with that ratio, and
   [div0] the DIVISION-BY-ZERO condition. *)
Record sbcl_arith_ops (h : string -> list sv -> cres) (ratio to_double : Z -> Z -> sv) (one_d div0 : sv) : Prop := {
 sbcl_fixnum_int : forall z, exists r, h "TYPEP" [zs z; VSym "FIXNUM"] = CRet (hb r);
 sbcl_double_int : forall z, h "TYPEP" [zs z; VSym "DOUBLE-FLOAT"] = CRet VNil;
 sbcl_integer_or_double_int : forall z, h "TYPEP" [zs z; SL [Sy "OR"; Sy "INTEGER"; Sy "DOUBLE-FLOAT"]] = CRet T;
 sbcl_add : forall x y, h "+" [zs x; zs y] = CRet (zs (x + y));
 sbcl_sub : forall x y, h "-" [zs x; zs y] = CRet (zs (x - y));
 sbcl_mul : forall x y, h "*" [zs x; zs y] = CRet (zs (x * y));
 sbcl_zerop : forall z, h "ZEROP" [zs z] = CRet (hb (Z.eqb z 0));
 sbcl_div : forall x y, h "/" [zs x; zs y] =
   if Z.eqb y 0 then CRaise div0 else if Z.eqb (Z.rem x y) 0 then CRet (zs (Z.quot x y)) else CRet (ratio x y);
 sbcl_integerp_int : forall z, h "INTEGERP" [zs z] = CRet T;
 sbcl_integerp_ratio : forall x y, h "INTEGERP" [ratio x y] = CRet VNil;
 sbcl_coerce_one : h "COERCE" [VNum "1.0"; VSym "DOUBLE-FLOAT"] = CRet one_d;
 sbcl_float_ratio : forall x y, h "*" [one_d; ratio x y] = CRet (to_double x y);
 (* Used only for the divergence theorem: classification of a symbol. *)
 sbcl_fixnum_sym : forall s, h "TYPEP" [VSym s; VSym "FIXNUM"] = CRet VNil }.
Lemma ce_let : forall h m env x init body r, ceval m h env init = r ->
 ceval (S m) h env (SL [Sy "LET"; SL [SL [Sy x; init]]; body]) =
 match r with CRet v => ceval m h ((x, v) :: env) body | o => o end.
Proof. intros; cbn; rewrite H; destruct r; reflexivity. Qed.
Lemma ce_or_left : forall h m env x y v, ceval m h env x = CRet v -> truthy v = true ->
 ceval (S m) h env (SL [Sy "OR"; x; y]) = CRet v.
Proof. intros; rewrite (ce_or2 h m env x y v H), H0; reflexivity. Qed.
Section Arith.
Variables (h : string -> list sv -> cres) (ratio to_double : Z -> Z -> sv) (one_d div0 : sv).
Hypothesis A : sbcl_arith_ops h ratio to_double one_d div0.
Lemma dp_int : forall m env v z, ceval (S (S (S m))) h env v = CRet (zs z) ->
 ceval (S (S (S (S m)))) h env (SL [Sy "shen-cl.double-precision"; v]) = CRet (zs z).
Proof.
 intros m env v z Hv.
 rewrite (ce_def1 _ _ _ _ _ (zs z) ["X"] double_precision_body) by (reflexivity || exact Hv).
 unfold double_precision_body.
 rewrite (ce_if _ _ _ _ _ _ T) by (host; [cvar|reflexivity|apply (sbcl_integer_or_double_int _ _ _ _ _ A)]).
 cbn [truthy]. cvar.
Qed.
Lemma and_fx : forall m x y, exists r, ceval (S (S (S (S m)))) h (env2 (zs x) (zs y)) (SL [Sy "AND"; fx "X"; fx "Y"]) = CRet (hb r) /\
 (forall z, h "TYPEP" [zs z; VSym "FIXNUM"] = CRet T -> r = true \/ True).
Proof.
 intros m x y. destruct (sbcl_fixnum_int _ _ _ _ _ A x) as [r1 E1]. destruct (sbcl_fixnum_int _ _ _ _ _ A y) as [r2 E2].
 exists (r1 && r2)%bool. split; [|auto].
 rewrite (ce_and2 _ _ _ _ _ (hb r1)) by (host; [cvar|reflexivity|exact E1]).
 destruct r1; cbn [truthy hb andb]; [|reflexivity].
 host; [cvar|reflexivity|exact E2].
Qed.
Lemma and_df : forall m x y, ceval (S (S (S (S m)))) h (env2 (zs x) (zs y)) (SL [Sy "AND"; df "X"; df "Y"]) = CRet VNil.
Proof.
 intros. rewrite (ce_and2 _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (sbcl_double_int _ _ _ _ _ A)]). reflexivity.
Qed.
Lemma dp_args : forall m x y g, plain g = true -> assoc g program = None ->
 ceval (S (S (S (S (S m))))) h (env2 (zs x) (zs y)) (SL [Sy g; dp "X"; dp "Y"]) = h g [zs x; zs y].
Proof. intros m x y g P G. eapply ce_host2; [exact P|exact G|apply dp_int; cvar|apply dp_int; cvar|reflexivity]. Qed.
(* For every pair of exact integers (fixnum or bignum, any signs) the
   captured additive wrappers return the exact sum and difference. *)
Theorem additive_int : forall g (o : Z -> Z -> Z), plain g = true -> assoc g program = None ->
 (forall x y, h g [zs x; zs y] = CRet (zs (o x y))) ->
 forall x y n, n >= 10 -> ceval n h (env2 (zs x) (zs y)) (additive_body g) = CRet (zs (o x y)).
Proof.
 intros g o P G8 Ho x y n Hn.
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold additive_body. destruct (and_fx (S (S (S (S (S m))))) x y) as [r [Er _]].
 destruct r.
 - rewrite (ce_cond_hit _ _ _ _ _ _ T) by (exact Er || reflexivity). eapply ce_host2; [exact P|exact G8|cvar|cvar|apply Ho].
 - rewrite ce_cond_miss by exact Er. rewrite ce_cond_miss by apply and_df.
   rewrite (ce_cond_hit _ _ _ _ _ _ T) by reflexivity. rewrite dp_args by assumption. apply Ho.
Qed.
Theorem add_int : forall x y n, n >= 10 -> ceval n h (env2 (zs x) (zs y)) (additive_body "+") = CRet (zs (x + y)).
Proof. intros. apply additive_int; try reflexivity; auto. apply (sbcl_add _ _ _ _ _ A). Qed.
Theorem subtract_int : forall x y n, n >= 10 -> ceval n h (env2 (zs x) (zs y)) (additive_body "-") = CRet (zs (x - y)).
Proof. intros. apply additive_int; try reflexivity; auto. apply (sbcl_sub _ _ _ _ _ A). Qed.
Lemma zs0 : zs 0 = VNum "0". Proof. reflexivity. Qed.
Theorem multiply_int : forall x y n, n >= 10 -> ceval n h (env2 (zs x) (zs y)) multiply_body = CRet (zs (x * y)).
Proof.
 intros x y n Hn.
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold multiply_body. destruct (and_fx (S (S (S (S (S m))))) x y) as [r [Er _]].
 destruct r.
 - rewrite (ce_cond_hit _ _ _ _ _ _ T) by (exact Er || reflexivity). host; [cvar|cvar|apply (sbcl_mul _ _ _ _ _ A)].
 - rewrite ce_cond_miss by exact Er. rewrite ce_cond_miss by apply and_df.
   destruct (Z.eqb x 0) eqn:X0.
   + apply Z.eqb_eq in X0; subst.
     rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (apply ce_or_left with (v := T); [|reflexivity];
       host; [cvar|apply (sbcl_zerop _ _ _ _ _ A)])).
     reflexivity.
   + destruct (Z.eqb y 0) eqn:Y0.
     * apply Z.eqb_eq in Y0; subst. rewrite Z.mul_0_r.
       rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (rewrite (ce_or2 _ _ _ _ _ VNil) by (host; [cvar|rewrite (sbcl_zerop _ _ _ _ _ A), X0; reflexivity]);
         host; [cvar|apply (sbcl_zerop _ _ _ _ _ A)])).
       reflexivity.
     * rewrite ce_cond_miss by (rewrite (ce_or2 _ _ _ _ _ VNil) by (host; [cvar|rewrite (sbcl_zerop _ _ _ _ _ A), X0; reflexivity]);
         host; [cvar|rewrite (sbcl_zerop _ _ _ _ _ A), Y0; reflexivity]).
       rewrite (ce_cond_hit _ _ _ _ _ _ T) by reflexivity. rewrite dp_args by reflexivity. apply (sbcl_mul _ _ _ _ _ A).
Qed.
(* Discovered divergence: an exact zero absorbs a non-number. The wrapper
   answers 0 where KLambda's * rule is a domain error (XPrim KLSyntax.KLSyntax.PMul); SBCL
   agrees with this theorem natively (ports/shen-cl-primitive-samples.lisp). *)
Theorem multiply_zero_absorbs_symbol : forall s n, n >= 10 ->
 ceval n h (env2 (zs 0) (VSym s)) multiply_body = CRet (zs 0) /\
 forall Pr st t, KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PMul Z.mul
   [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt 0); KLValue.KLValue.VSym t] st = KLSemantics.KLSemantics.dom KLSyntax.KLSyntax.PMul.
Proof.
 intros s n Hn. split; [|reflexivity].
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold multiply_body. destruct (sbcl_fixnum_int _ _ _ _ _ A 0) as [r1 E1].
 rewrite ce_cond_miss.
 2: { rewrite (ce_and2 _ _ _ _ _ (hb r1)) by (host; [cvar|reflexivity|exact E1]).
      destruct r1; cbn [truthy hb]; [|reflexivity]. host; [cvar|reflexivity|apply (sbcl_fixnum_sym _ _ _ _ _ A)]. }
 rewrite ce_cond_miss.
 2: { rewrite (ce_and2 _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (sbcl_double_int _ _ _ _ _ A)]). reflexivity. }
 rewrite (ce_cond_hit _ _ _ _ _ _ T) by (reflexivity || (apply ce_or_left with (v := T); [|reflexivity];
   host; [cvar|apply (sbcl_zerop _ _ _ _ _ A)])).
 reflexivity.
Qed.
(* Division: exact quotient when divisible, the host double nearest x/y
   otherwise (never a ratio), and the DIVISION-BY-ZERO condition for y = 0. *)
Theorem divide_int : forall x y n, n >= 10 -> ceval n h (env2 (zs x) (zs y)) divide_body =
 if Z.eqb y 0 then CRaise div0 else if Z.eqb (Z.rem x y) 0 then CRet (zs (Z.quot x y)) else CRet (to_double x y).
Proof.
 intros x y n Hn.
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold divide_body. rewrite (ce_let _ _ _ _ _ _ (h "/" [zs x; zs y])) by (apply dp_args; reflexivity).
 rewrite (sbcl_div _ _ _ _ _ A).
 destruct (Z.eqb y 0); [reflexivity|]. destruct (Z.eqb (Z.rem x y) 0).
 - rewrite (ce_if _ _ _ _ _ _ T) by (host; [cvar|apply (sbcl_integerp_int _ _ _ _ _ A)]). cbn [truthy]. cvar.
 - rewrite (ce_if _ _ _ _ _ _ VNil) by (host; [cvar|apply (sbcl_integerp_ratio _ _ _ _ _ A)]). cbn [truthy].
   host; [|cvar|apply (sbcl_float_ratio _ _ _ _ _ A)].
   host; [reflexivity|reflexivity|apply (sbcl_coerce_one _ _ _ _ _ A)].
Qed.
(* The formal rule slots: rule_arith for + - * on exact integers and
   rule_div, whose non-integral case is the profile slot int_div_inexact; the
   wrapper agrees with it exactly when that slot is pinned to the host's
   correctly-rounded conversion [to_double] (OB-NUMERIC-PROFILE). *)
Theorem arith_refines_rules : forall Pr st x y n, n >= 10 ->
 (KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PAdd Z.add [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (x + y))) st /\
  ceval n h (env2 (zs x) (zs y)) (additive_body "+") = CRet (zs (x + y))) /\
 (KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PSub Z.sub [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (x - y))) st /\
  ceval n h (env2 (zs x) (zs y)) (additive_body "-") = CRet (zs (x - y))) /\
 (KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PMul Z.mul [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
   = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (x * y))) st /\
  ceval n h (env2 (zs x) (zs y)) multiply_body = CRet (zs (x * y))) /\
 ((y = 0%Z /\ KLSemantics.KLSemantics.rule_div Pr [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
     = KLSemantics.KLSemantics.throw KLValue.KLValue.XDivZero /\ ceval n h (env2 (zs x) (zs y)) divide_body = CRaise div0) \/
  (y <> 0%Z /\ Z.rem x y = 0%Z /\
   KLSemantics.KLSemantics.rule_div Pr [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
     = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt (Z.quot x y))) st /\
   ceval n h (env2 (zs x) (zs y)) divide_body = CRet (zs (Z.quot x y))) \/
  (y <> 0%Z /\ Z.rem x y <> 0%Z /\
   KLSemantics.KLSemantics.rule_div Pr [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st
     = KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (KLValue.KLValue.int_div_inexact Pr x y)) st /\
   ceval n h (env2 (zs x) (zs y)) divide_body = CRet (to_double x y))).
Proof.
 intros Pr st x y n Hn. split; [split; [reflexivity|apply add_int; lia]|].
 split; [split; [reflexivity|apply subtract_int; lia]|]. split; [split; [reflexivity|apply multiply_int; lia]|].
 rewrite divide_int by lia.
 destruct (Z.eqb y 0) eqn:Y0.
 - left. apply Z.eqb_eq in Y0; subst. split; [reflexivity|split; reflexivity].
 - right. apply Z.eqb_neq in Y0.
   assert (D : KLSemantics.KLSemantics.rule_div Pr [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt x); KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt y)] st =
     KLSemantics.KLSemantics.ret (KLValue.KLValue.VNum (if Z.eqb (Z.rem x y) 0 then KLSyntax.KLSyntax.NInt (Z.quot x y) else KLValue.KLValue.int_div_inexact Pr x y)) st)
     by (destruct y; [contradiction|reflexivity|reflexivity]).
   rewrite D. destruct (Z.eqb (Z.rem x y) 0) eqn:R0.
   + left. apply Z.eqb_eq in R0. auto.
   + right. apply Z.eqb_neq in R0. auto.
Qed.
End Arith.
(* Anti-vacuity for the arithmetic contracts: a concrete table (exact
   integers read back from their canonical spellings, ratios and the double
   1.0d0 as distinct host objects). It is not a model of SBCL. *)
Definition zinv (s : string) : option Z := option_map Z.of_int (NilZero.int_of_string s).
Lemma zinv_zs : forall z, zinv (Native.spelling z) = Some z.
Proof.
 intro z. unfold zinv, Native.spelling. rewrite NilZero.isi.
 - cbn. rewrite DecimalZ.of_to. reflexivity.
 - destruct z; cbn; try discriminate; intro E; injection E; apply DecimalPos.Unsigned.to_uint_nonnil.
 - destruct z; cbn; try discriminate; intro E; injection E; apply DecimalPos.Unsigned.to_uint_nonnil.
Qed.
Definition mratio (x y : Z) : sv := CLLowering.VObj 0.
Definition mdouble (x y : Z) : sv := CLLowering.VObj 2.
Definition int2 (f : Z -> Z -> cres) (vs : list sv) : cres := match vs with
 | [VNum s; VNum t] => match zinv s, zinv t with Some x, Some y => f x y | _, _ => CUnsup end
 | _ => CUnsup end.
Definition model_arith (f : string) (vs : list sv) : cres :=
 if String.eqb f "TYPEP" then match vs with
   | [VNum s; VSym "FIXNUM"] => CRet T
   | [VSym _; VSym "FIXNUM"] => CRet VNil
   | [VNum _; VSym "DOUBLE-FLOAT"] => CRet VNil
   | [VNum _; _] => CRet T
   | _ => CUnsup end
 else if String.eqb f "+" then int2 (fun x y => CRet (zs (x + y))) vs
 else if String.eqb f "-" then int2 (fun x y => CRet (zs (x - y))) vs
 else if String.eqb f "*" then match vs with
   | [CLLowering.VObj 1; CLLowering.VObj 0] => CRet (CLLowering.VObj 2)
   | _ => int2 (fun x y => CRet (zs (x * y))) vs end
 else if String.eqb f "ZEROP" then match vs with
   | [VNum s] => match zinv s with Some z => CRet (hb (Z.eqb z 0)) | None => CUnsup end | _ => CUnsup end
 else if String.eqb f "/" then int2 (fun x y => if Z.eqb y 0 then CRaise (CLLowering.VObj 3)
   else if Z.eqb (Z.rem x y) 0 then CRet (zs (Z.quot x y)) else CRet (mratio x y)) vs
 else if String.eqb f "INTEGERP" then match vs with [VNum _] => CRet T | [CLLowering.VObj 0] => CRet VNil | _ => CUnsup end
 else if String.eqb f "COERCE" then match vs with [VNum "1.0"; VSym "DOUBLE-FLOAT"] => CRet (CLLowering.VObj 1) | _ => CUnsup end
 else CUnsup.
Theorem model_arith_ops : sbcl_arith_ops model_arith mratio mdouble (CLLowering.VObj 1) (CLLowering.VObj 3).
Proof.
 constructor; intros; unfold model_arith, zs; cbn [String.eqb Ascii.eqb Bool.eqb]; try reflexivity.
 - exists true. reflexivity.
 - unfold int2. rewrite !zinv_zs. reflexivity.
 - unfold int2. rewrite !zinv_zs. reflexivity.
 - unfold int2. rewrite !zinv_zs. reflexivity.
 - rewrite zinv_zs. reflexivity.
 - unfold int2. rewrite !zinv_zs. reflexivity.
Qed.
End CLWrappers.
