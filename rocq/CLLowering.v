(* Shen-CL conditional lowering: inert source admission, an interpreter for
   the captured Shen definitions, and a small Common Lisp evaluation model.

   Pinned source: Shen-CL 4844072dde0208c3e4b99dcbfea58e4fdfd812e8,
   src/compiler.shen, definitions emit-boolean, optimise-boolean-check,
   optimise-boolean-sequence and emit-if, plus the enclosing package header.

   Evidence kinds kept separate here:
   - admission (admitted_lowering) is computed equality of the captured reader
     AST with the reviewed expected AST below;
   - the lowering function is obtained by interpreting the admitted AST with
     [run]; nothing below re-implements the lowering by hand;
   - the theorems quantify over every input datum, every Common Lisp world
     (state type, primitive relation, opaque forms) and every compile-expression
     function, under the named hypotheses in [primitive_contracts].

   Not modeled (explicit contracts, documented in docs/CL-PORT.md): SBCL
   execution and compilation, the CL reader and printer, the shen-cl.cl/kl
   helpers (modeled from overwrite.lsp/compiler.shen text), the Shen package
   system-function table, compile-expression itself, bind-accessor-chains, and
   diagnostic text of Boolean errors. *)
From Coq Require Import String List Bool Ascii Arith.
From Buri Require CLPortGuard CLPortCapture.
Import ListNotations.
Open Scope string_scope.
Arguments String.eqb : simpl nomatch.

(* ---------- 1. Inert Shen surface syntax and reviewed expected AST ---------- *)

Inductive src := SSym (s : string) | SStr (s : string) | SNum (s : string) | SBar
 | SParen (xs : srcs) | SBrack (xs : srcs)
with srcs := SNil | SCons (x : src) (xs : srcs).

Fixpoint src_eqb (a b : src) : bool :=
 match a, b with
 | SSym x, SSym y | SStr x, SStr y | SNum x, SNum y => String.eqb x y
 | SBar, SBar => true
 | SParen x, SParen y | SBrack x, SBrack y => srcs_eqb x y
 | _, _ => false end
with srcs_eqb (a b : srcs) : bool :=
 match a, b with
 | SNil, SNil => true
 | SCons x xs, SCons y ys => src_eqb x y && srcs_eqb xs ys
 | _, _ => false end.

Scheme src_ind2 := Induction for src Sort Prop with srcs_ind2 := Induction for srcs Sort Prop.

Lemma src_eqb_sound : forall a b, src_eqb a b = true -> a = b.
Proof.
 apply (src_ind2 (fun a => forall b, src_eqb a b = true -> a = b)
                 (fun a => forall b, srcs_eqb a b = true -> a = b));
 intros; destruct b; simpl in *; try discriminate;
 try (apply String.eqb_eq in H; subst; reflexivity);
 try (apply String.eqb_eq in H0; subst; reflexivity);
 try reflexivity;
 try (f_equal; auto; fail).
 apply andb_true_iff in H1 as [H1 H2]. f_equal; auto.
Qed.

Fixpoint mk (l : list src) : srcs := match l with [] => SNil | x :: r => SCons x (mk r) end.
Definition P l := SParen (mk l).
Definition B l := SBrack (mk l).
Definition A := SSym.
Definition cl_ x := P [A "cl"; A x].
Definition kl_ x := P [A "kl"; A x].
Definition opt_ x := P [A "optimise-boolean-check"; A x].
Definition ce_ x := P [A "compile-expression"; A x; A "Scope"].
Definition is_ x y := P [A "="; A x; cl_ y].

Definition expected_package := P [A "package"; A "shen-cl"; B (map A
 ["progn"; "quote"; "null"; "car"; "cdr"; "list-length"; "t"; "nil";
  "numberp"; "stringp"; "consp"; "funcall";
  "list"; "eq"; "eql"; "equal"; "equalp"; "let*";
  "setq";
  "shen.pvar?"; "shen-cl.absvector-p"; "shen-cl.integral-p";
  "shen-cl.boolean-p"; "shen-cl.pvar-p";
  "lisp.defun"; "lisp.lambda"; "lisp.block"; "lisp.";
  "%%return"; "return"; "%%goto-label"; "go";
  "%%let-label"; "block"; "tagbody"])].

Definition expected_emit_boolean := P [A "define"; A "emit-boolean";
 A "Predicate"; A "->"; B [cl_ "if"; A "Predicate"; B [cl_ "quote"; A "true"]; B [cl_ "quote"; A "false"]]].

Definition equal2 x y := B [A "equal?"; x; y].
Definition expected_optimise := P ([A "define"; A "optimise-boolean-check";
 B [A "If"; A "Test"; B [A "Quote"; A "true"]; B [A "Quote"; A "false"]]; A "->"; A "Test";
   A "where"; P [A "and"; is_ "If" "if"; is_ "Quote" "quote"];
 B [A "Let"; A "Bindings"; A "Body"]; A "->"; B [A "Let"; A "Bindings"; opt_ "Body"];
   A "where"; P [A "or"; is_ "Let" "let"; is_ "Let" "let*"];
 B [A "Progn"; SBar; A "Forms"]; A "->"; B [A "Progn"; SBar; P [A "optimise-boolean-sequence"; A "Forms"]];
   A "where"; is_ "Progn" "progn";
 B [A "If"; A "Test"; A "Then"; A "Else"]; A "->"; B [A "If"; A "Test"; opt_ "Then"; opt_ "Else"];
   A "where"; is_ "If" "if";
 B [A "cons?"; A "X"]; A "->"; B [cl_ "consp"; A "X"];
 B [A "string?"; A "X"]; A "->"; B [cl_ "stringp"; A "X"];
 B [A "number?"; A "X"]; A "->"; B [cl_ "numberp"; A "X"];
 B [A "empty?"; A "X"]; A "->"; B [cl_ "null"; A "X"];
 B [A "and"; A "P"; A "Q"]; A "->"; B [cl_ "and"; opt_ "P"; opt_ "Q"];
 B [A "or"; A "P"; A "Q"]; A "->"; B [cl_ "or"; opt_ "P"; opt_ "Q"];
 B [A "not"; A "P"]; A "->"; B [cl_ "not"; opt_ "P"];
 equal2 (A "X") (B [A "Quote"; B []]); A "->"; B [cl_ "null"; A "X"]; A "where"; is_ "Quote" "quote";
 equal2 (B [A "Quote"; B []]) (A "X"); A "->"; B [cl_ "null"; A "X"]; A "where"; is_ "Quote" "quote";
 equal2 (B [A "fail"]) (A "X"); A "->"; B [cl_ "eq"; B [A "fail"]; A "X"];
 equal2 (A "X") (B [A "fail"]); A "->"; B [cl_ "eq"; A "X"; B [A "fail"]];
 equal2 (A "S") (A "X"); A "->"; B [cl_ "equal"; A "S"; A "X"]; A "where"; P [A "string?"; A "S"];
 equal2 (A "X") (A "S"); A "->"; B [cl_ "equal"; A "X"; A "S"]; A "where"; P [A "string?"; A "S"];
 equal2 (A "X") (A "N"); A "->"; B [kl_ "numeric-equal"; A "X"; A "N"]; A "where"; P [A "number?"; A "N"];
 equal2 (A "N") (A "X"); A "->"; B [kl_ "numeric-equal"; A "X"; A "N"]; A "where"; P [A "number?"; A "N"];
 equal2 (A "X") (B [A "Quote"; A "S"]); A "->"; B [cl_ "eq"; A "X"; B [A "Quote"; A "S"]];
   A "where"; P [A "="; cl_ "quote"; A "Quote"];
 equal2 (B [A "Quote"; A "S"]) (A "X"); A "->"; B [cl_ "eq"; A "X"; B [A "Quote"; A "S"]];
   A "where"; P [A "="; cl_ "quote"; A "Quote"];
 equal2 (A "X") (A "Y"); A "->"; B [kl_ "absequal"; A "X"; A "Y"];
 B [A "greater?"; A "X"; A "Y"]; A "->"; B [cl_ ">"; A "X"; A "Y"];
 B [A "greater-than-or-equal-to?"; A "X"; A "Y"]; A "->"; B [cl_ ">="; A "X"; A "Y"];
 B [A "less?"; A "X"; A "Y"]; A "->"; B [cl_ "<"; A "X"; A "Y"];
 B [A "less-than-or-equal-to?"; A "X"; A "Y"]; A "->"; B [cl_ "<="; A "X"; A "Y"];
 B [A "Quote"; A "true"]; A "->"; cl_ "t"; A "where"; is_ "Quote" "quote";
 B [A "Quote"; A "false"]; A "->"; cl_ "nil"; A "where"; is_ "Quote" "quote";
 A "Exp"; A "->"; B [A "true?"; A "Exp"]]).

Definition expected_sequence := P [A "define"; A "optimise-boolean-sequence";
 B [A "Last"]; A "->"; B [opt_ "Last"];
 B [A "First"; SBar; A "Rest"]; A "->"; B [A "First"; SBar; P [A "optimise-boolean-sequence"; A "Rest"]]].

Definition expected_emit_if := P [A "define"; A "emit-if";
 A "true"; A "Then"; A "_"; A "Scope"; A "->"; ce_ "Then";
 A "false"; A "_"; A "Else"; A "Scope"; A "->"; ce_ "Else";
 A "Test"; A "Then"; A "Else"; A "Scope";
 A "->"; B [cl_ "if"; P [A "optimise-boolean-check"; ce_ "Test"]; ce_ "Then"; ce_ "Else"]].

(* Symbols occurring in the four definitions that Shen 43.1's
   (get shen external-symbols) contains. Reviewed against the kernel source
   declarations.shen; the capture also records the capture host's answer. *)
Definition reviewed_sysfuncs : list string :=
 ["define"; "->"; "if"; "true"; "false"; "where"; "and"; "="; "or"; "let";
  "cons?"; "string?"; "number?"; "empty?"; "null"; "not"; "fail";
  ">"; ">="; "<"; "<="; "_"].

Record lowering_source := mk_lowering_source {
 ls_package : src; ls_emit_boolean : src; ls_optimise : src;
 ls_sequence : src; ls_emit_if : src; ls_sysfuncs : list string }.

Definition mem (s : string) (l : list string) := existsb (String.eqb s) l.
Definition set_eqb (a b : list string) :=
 forallb (fun x => mem x b) a && forallb (fun x => mem x a) b.

Definition admitted_lowering (L : lowering_source) : bool :=
 src_eqb (ls_package L) expected_package && src_eqb (ls_emit_boolean L) expected_emit_boolean
 && src_eqb (ls_optimise L) expected_optimise && src_eqb (ls_sequence L) expected_sequence
 && src_eqb (ls_emit_if L) expected_emit_if && set_eqb (ls_sysfuncs L) reviewed_sysfuncs.

Theorem lowering_admission_exact : forall L, admitted_lowering L = true ->
 ls_package L = expected_package /\ ls_emit_boolean L = expected_emit_boolean /\
 ls_optimise L = expected_optimise /\ ls_sequence L = expected_sequence /\
 ls_emit_if L = expected_emit_if.
Proof.
 intros L H. unfold admitted_lowering in H.
 repeat (apply andb_true_iff in H as [H ?]).
 repeat split; apply src_eqb_sound; assumption.
Qed.

(* ---------- 2. Shen data and package resolution ---------- *)

(* Data for both compile-time code and CL run-time values. VObj stands for
   host objects (functions, vectors, conditions) with no source syntax. *)
Inductive sv := VSym (s : string) | VStr (s : string) | VNum (s : string)
 | VObj (n : nat) | VNil | VCons (a b : sv).

Fixpoint sv_eqb (a b : sv) : bool :=
 match a, b with
 | VSym x, VSym y | VStr x, VStr y | VNum x, VNum y => String.eqb x y
 | VObj x, VObj y => Nat.eqb x y
 | VNil, VNil => true
 | VCons a b, VCons c d => sv_eqb a c && sv_eqb b d
 | _, _ => false end.

Lemma sv_eqb_eq : forall a b, sv_eqb a b = true <-> a = b.
Proof.
 induction a; destruct b; simpl; split; intros H; try discriminate; try congruence;
 try (apply String.eqb_eq in H; subst; reflexivity);
 try (injection H as <-; apply String.eqb_refl);
 try (apply Nat.eqb_eq in H; subst; reflexivity);
 try (injection H as <-; apply Nat.eqb_refl).
 - apply andb_true_iff in H as [H1 H2]. apply IHa1 in H1. apply IHa2 in H2. subst. reflexivity.
 - injection H as <- <-. apply andb_true_iff. split; [apply IHa1 | apply IHa2]; reflexivity.
Qed.

Definition upcase_ascii (c : ascii) : ascii :=
 let n := nat_of_ascii c in if Nat.leb 97 n && Nat.leb n 122 then ascii_of_nat (n - 32) else c.
Fixpoint upcase (s : string) : string :=
 match s with EmptyString => EmptyString | String c r => String (upcase_ascii c) (upcase r) end.

Definition is_variable (s : string) : bool :=
 match s with String c _ => let n := nat_of_ascii c in Nat.leb 65 n && Nat.leb n 90 | _ => false end.
Fixpoint repeated_h (c : ascii) (s : string) : bool :=
 match s with
 | String a (String b (String d EmptyString)) => Ascii.eqb a c && Ascii.eqb b c && Ascii.eqb d c
 | String a r => Ascii.eqb a c && repeated_h c r
 | EmptyString => false end.
(* Kernel sng?/dbl?: three or more underscores / equals signs. *)
Definition sng (s : string) := repeated_h "_"%char s.
Definition dbl (s : string) := repeated_h "="%char s.

(* Kernel 43.1 shen.internal? for a symbol spelling; Shen-CL additionally
   treats lisp.-prefixed symbols as system functions. *)
Definition internal (p : string) (ext : list string) (s : string) : bool :=
 negb (mem s ext) && negb (sng s) && negb (dbl s)
 && negb (mem s reviewed_sysfuncs || String.prefix "lisp." s) && negb (is_variable s)
 && negb (String.prefix "shen." s) && negb (String.prefix (p ++ ".") s).
Definition resolve (p : string) (ext : list string) (s : string) : string :=
 if internal p ext s then p ++ "." ++ s else s.

Fixpoint srcs_list (xs : srcs) : list src := match xs with SNil => [] | SCons x r => x :: srcs_list r end.
Definition sym_of (x : src) : option string := match x with SSym s => Some s | _ => None end.
Fixpoint all_syms (xs : list src) : option (list string) :=
 match xs with [] => Some []
 | x :: r => match sym_of x, all_syms r with Some s, Some l => Some (s :: l) | _, _ => None end end.
Definition package_of (x : src) : option (string * list string) :=
 match x with
 | SParen (SCons (SSym "package") (SCons (SSym p) (SCons (SBrack ext) SNil))) =>
   match all_syms (srcs_list ext) with Some l => Some (p, l) | None => None end
 | _ => None end.

(* ---------- 3. The Shen define fragment ---------- *)

Inductive pat := PVar (x : string) | PWild | PConst (v : sv) | PCons (p q : pat).
Inductive expr := EVar (x : string) | EConst (v : sv) | ECons (a b : expr) | EApp (f : string) (args : list expr).
Record clause := mk_clause { c_pats : list pat; c_rhs : expr; c_guard : option expr }.

Section Compile.
Variable r : string -> string.
(* Patterns: variables, _, symbol and string constants, [] and [..|..].
   Numeric constants and (..) patterns are unsupported, not guessed. *)
Fixpoint to_pat (x : src) : option pat :=
 match x with
 | SSym s => if String.eqb s "_" then Some PWild
             else if is_variable s then Some (PVar s) else Some (PConst (VSym (r s)))
 | SStr s => Some (PConst (VStr s))
 | SBrack xs => brack_pat xs
 | _ => None end
with brack_pat (xs : srcs) : option pat :=
 match xs with
 | SNil => Some (PConst VNil)
 | SCons SBar (SCons t SNil) => to_pat t
 | SCons SBar _ => None
 | SCons x rest => match to_pat x, brack_pat rest with Some p, Some q => Some (PCons p q) | _, _ => None end
 end.
Fixpoint to_expr (x : src) : option expr :=
 match x with
 | SSym s => if is_variable s then Some (EVar s) else Some (EConst (VSym (r s)))
 | SStr s => Some (EConst (VStr s))
 | SNum s => Some (EConst (VNum s))
 | SBar => None
 | SParen (SCons (SSym f) args) =>
   if is_variable f then None else
   match args_expr args with Some l => Some (EApp (r f) l) | None => None end
 | SParen _ => None
 | SBrack xs => brack_expr xs end
with args_expr (xs : srcs) : option (list expr) :=
 match xs with SNil => Some []
 | SCons x rest => match to_expr x, args_expr rest with Some e, Some l => Some (e :: l) | _, _ => None end end
with brack_expr (xs : srcs) : option expr :=
 match xs with
 | SNil => Some (EConst VNil)
 | SCons SBar (SCons t SNil) => to_expr t
 | SCons SBar _ => None
 | SCons x rest => match to_expr x, brack_expr rest with Some a, Some b => Some (ECons a b) | _, _ => None end
 end.
Fixpoint parse_clauses (xs : list src) (acc : list pat) : option (list clause) :=
 match xs with
 | [] => match acc with [] => Some [] | _ => None end
 | SSym "->" :: rhs :: SSym "where" :: g :: rest =>
   match to_expr rhs, to_expr g, parse_clauses rest [] with
   | Some e, Some ge, Some cs => Some (mk_clause (rev acc) e (Some ge) :: cs)
   | _, _, _ => None end
 | SSym "->" :: rhs :: rest =>
   match to_expr rhs, parse_clauses rest [] with
   | Some e, Some cs => Some (mk_clause (rev acc) e None :: cs)
   | _, _ => None end
 | SSym "<-" :: _ => None
 | p :: rest => match to_pat p with Some q => parse_clauses rest (q :: acc) | None => None end
 end.
Definition same_arity (cs : list clause) :=
 match cs with [] => false | c :: r => forallb (fun d => Nat.eqb (length (c_pats d)) (length (c_pats c))) r end.
Definition define_of (x : src) : option (string * list clause) :=
 match x with
 | SParen (SCons (SSym "define") (SCons (SSym n) rest)) =>
   match parse_clauses (srcs_list rest) [] with
   | Some cs => if same_arity cs then Some (r n, cs) else None
   | None => None end
 | _ => None end.
End Compile.

Definition defs := list (string * list clause).
Definition OPT := "shen-cl.optimise-boolean-check".
Definition SEQ := "shen-cl.optimise-boolean-sequence".
Definition EMIT_IF := "shen-cl.emit-if".
Definition EMIT_BOOL := "shen-cl.emit-boolean".
Definition CE := "shen-cl.compile-expression".

Definition compile_lowering (L : lowering_source) : option defs :=
 match package_of (ls_package L) with
 | Some (p, ext) =>
   let r := resolve p ext in
   match define_of r (ls_emit_boolean L), define_of r (ls_optimise L),
         define_of r (ls_sequence L), define_of r (ls_emit_if L) with
   | Some d1, Some d2, Some d3, Some d4 =>
     if String.eqb (fst d1) EMIT_BOOL && String.eqb (fst d2) OPT && String.eqb (fst d3) SEQ
        && String.eqb (fst d4) EMIT_IF then Some [d1; d2; d3; d4] else None
   | _, _, _, _ => None end
 | None => None end.

Definition expected_lowering := mk_lowering_source expected_package expected_emit_boolean
 expected_optimise expected_sequence expected_emit_if reviewed_sysfuncs.

Definition expected_defs : defs :=
 Eval vm_compute in match compile_lowering expected_lowering with Some d => d | None => [] end.
Lemma compile_expected : compile_lowering expected_lowering = Some expected_defs.
Proof. vm_compute. reflexivity. Qed.

Definition lowering_defs (L : lowering_source) : defs :=
 match compile_lowering L with Some d => d | None => [] end.
Lemma admitted_defs : forall L, admitted_lowering L = true -> lowering_defs L = expected_defs.
Proof.
 intros L H. destruct (lowering_admission_exact L H) as [H1 [H2 [H3 [H4 H5]]]].
 unfold lowering_defs, compile_lowering. rewrite H1, H2, H3, H4, H5.
 change (match compile_lowering expected_lowering with Some d => d | None => [] end = expected_defs).
 rewrite compile_expected. reflexivity.
Qed.

(* ---------- 4. Interpreter for the admitted definitions ---------- *)

(* Distinct outcomes: a value, pattern-match failure (a compile-time error in
   Shen-CL), an unsupported construct, or exhausted fuel. *)
Inductive lres := LOk (v : sv) | LNoMatch | LUnsupported | LFuel.
Definition binding := list (string * sv).
Fixpoint lookup (x : string) (e : binding) : option sv :=
 match e with [] => None | (y, v) :: r => if String.eqb x y then Some v else lookup x r end.
Fixpoint assoc {T} (x : string) (l : list (string * T)) : option T :=
 match l with [] => None | (y, v) :: r => if String.eqb x y then Some v else assoc x r end.

(* A repeated pattern variable is Shen's equality test. Structural equality
   agrees with Shen-CL's absequal on number- and object-free data; any other
   unequal comparison is reported unsupported rather than guessed. *)
Fixpoint plain (v : sv) : bool :=
 match v with VNum _ | VObj _ => false | VCons a b => plain a && plain b | _ => true end.
Inductive mres := MOk (s : binding) | MNo | MUnsup.
Fixpoint match_pat (p : pat) (v : sv) (s : binding) : mres :=
 match p with
 | PWild => MOk s
 | PVar x => match lookup x s with
   | None => MOk ((x, v) :: s)
   | Some w => if sv_eqb w v then MOk s else if plain w && plain v then MNo else MUnsup end
 | PConst c => if sv_eqb c v then MOk s else MNo
 | PCons p q => match v with
   | VCons a b => match match_pat p a s with MOk s' => match_pat q b s' | m => m end
   | _ => MNo end end.
Fixpoint match_pats (ps : list pat) (vs : list sv) (s : binding) : mres :=
 match ps, vs with
 | [], [] => MOk s
 | p :: ps, v :: vs => match match_pat p v s with MOk s' => match_pats ps vs s' | m => m end
 | _, _ => MUnsup end.

Definition shen_bool (b : bool) := if b then VSym "true" else VSym "false".
Definition is_true v := sv_eqb v (VSym "true").
Definition is_false v := sv_eqb v (VSym "false").
Definition symbolic v := match v with VSym _ | VNil => true | _ => false end.
Definition is_str v := match v with VStr _ => true | _ => false end.
Definition is_num v := match v with VNum _ => true | _ => false end.
(* overwrite.lsp shen-cl.cl: intern the upcased name in SHEN. Inherited CL
   symbols keep their CL identity; NIL is the empty list. *)
Definition cl_sym (s : string) : sv := let u := upcase s in if String.eqb u "NIL" then VNil else VSym u.

Section Eval.
Variable call : string -> list sv -> lres.
Definition apply_builtin (f : string) (vals : list sv) : lres :=
 if String.eqb f "shen-cl.cl" then match vals with [VSym s] => LOk (cl_sym s) | _ => LUnsupported end
 else if String.eqb f "shen-cl.kl" then match vals with [v] => LOk v | _ => LUnsupported end
 else if String.eqb f "=" then match vals with
   | [a; b] => if sv_eqb a b then LOk (VSym "true")
              else if symbolic a || symbolic b then LOk (VSym "false") else LUnsupported
   | _ => LUnsupported end
 else if String.eqb f "string?" then match vals with [v] => LOk (shen_bool (is_str v)) | _ => LUnsupported end
 else if String.eqb f "number?" then match vals with [v] => LOk (shen_bool (is_num v)) | _ => LUnsupported end
 else call f vals.
Fixpoint eval_expr (s : binding) (e : expr) : lres :=
 match e with
 | EVar x => match lookup x s with Some v => LOk v | None => LUnsupported end
 | EConst v => LOk v
 | ECons a b => match eval_expr s a with
   | LOk x => match eval_expr s b with LOk y => LOk (VCons x y) | r => r end
   | r => r end
 | EApp f args =>
   if String.eqb f "and" || String.eqb f "or" then
     match args with
     | [a; b] => match eval_expr s a with
       | LOk x => if is_true x then (if String.eqb f "or" then LOk x else
                      match eval_expr s b with LOk y => if is_true y || is_false y then LOk y else LUnsupported | r => r end)
                  else if is_false x then (if String.eqb f "and" then LOk x else
                      match eval_expr s b with LOk y => if is_true y || is_false y then LOk y else LUnsupported | r => r end)
                  else LUnsupported
       | r => r end
     | _ => LUnsupported end
   else
   match (fix go (l : list expr) : sum (list sv) lres :=
            match l with [] => inl []
            | a :: r => match eval_expr s a with
              | LOk v => match go r with inl vs => inl (v :: vs) | inr x => inr x end
              | x => inr x end end) args with
   | inl vals => apply_builtin f vals
   | inr x => x end
 end.
Fixpoint apply_clauses (cs : list clause) (vals : list sv) : lres :=
 match cs with
 | [] => LNoMatch
 | c :: rest => match match_pats (c_pats c) vals [] with
   | MNo => apply_clauses rest vals
   | MUnsup => LUnsupported
   | MOk s => match c_guard c with
     | None => eval_expr s (c_rhs c)
     | Some g => match eval_expr s g with
       | LOk v => if is_true v then eval_expr s (c_rhs c)
                  else if is_false v then apply_clauses rest vals else LUnsupported
       | x => x end end end end.
End Eval.

(* compile-expression is an arbitrary function parameter [ce]. *)
Fixpoint run (fuel : nat) (D : defs) (ce : sv -> sv -> lres) (f : string) (vals : list sv) : lres :=
 match fuel with
 | O => LFuel
 | S n => match assoc f D with
   | Some cs => apply_clauses (fun g vs => if String.eqb g CE then
                    match vs with [a; b] => ce a b | _ => LUnsupported end
                  else run n D ce g vs) cs vals
   | None => LUnsupported end end.

(* Generic facts about clause selection. *)
Definition guard_holds (call : string -> list sv -> lres) (s : binding) (g : option expr) : Prop :=
 match g with None => True | Some g => exists v, eval_expr call s g = LOk v /\ is_true v = true end.
Lemma apply_clauses_sound : forall call cs vals r, apply_clauses call cs vals = LOk r ->
 exists c s, In c cs /\ match_pats (c_pats c) vals [] = MOk s /\ guard_holds call s (c_guard c)
   /\ eval_expr call s (c_rhs c) = LOk r.
Proof.
 intros call cs vals r. induction cs as [|c cs IH]; simpl; intros H; [discriminate|].
 destruct (match_pats (c_pats c) vals []) eqn:Hm; try discriminate.
 - destruct (c_guard c) as [g|] eqn:Hg.
   + destruct (eval_expr call s g) eqn:He; try discriminate.
     destruct (is_true v) eqn:Ht.
     * exists c, s. repeat split; auto. rewrite Hg. simpl. eauto.
     * destruct (is_false v); try discriminate. destruct (IH H) as [c' [s' [? ?]]]. exists c', s'. tauto.
   + exists c, s. repeat split; auto. rewrite Hg. simpl. exact I.
 - destruct (IH H) as [c' [s' [? ?]]]. exists c', s'. tauto.
Qed.

Definition opt_clauses : list clause := Eval vm_compute in
 match assoc OPT expected_defs with Some cs => cs | None => [] end.
Definition seq_clauses : list clause := Eval vm_compute in
 match assoc SEQ expected_defs with Some cs => cs | None => [] end.
Definition emit_if_clauses : list clause := Eval vm_compute in
 match assoc EMIT_IF expected_defs with Some cs => cs | None => [] end.
Definition emit_boolean_clauses : list clause := Eval vm_compute in
 match assoc EMIT_BOOL expected_defs with Some cs => cs | None => [] end.
Lemma assoc_opt : assoc OPT expected_defs = Some opt_clauses. Proof. vm_compute. reflexivity. Qed.
Lemma assoc_seq : assoc SEQ expected_defs = Some seq_clauses. Proof. vm_compute. reflexivity. Qed.
Lemma assoc_emit_if : assoc EMIT_IF expected_defs = Some emit_if_clauses. Proof. vm_compute. reflexivity. Qed.
Lemma assoc_emit_boolean : assoc EMIT_BOOL expected_defs = Some emit_boolean_clauses.
Proof. vm_compute. reflexivity. Qed.

(* ---------- 5. Common Lisp evaluation model ---------- *)

Notation f2 h a := (VCons (VSym h) (VCons a VNil)).
Notation f3 h a b := (VCons (VSym h) (VCons a (VCons b VNil))).
Notation f4 h a b c := (VCons (VSym h) (VCons a (VCons b (VCons c VNil)))).
Definition TRUEP := "shen-cl.true?".
Definition EQUALP := "shen-cl.equal?".

(* Heads evaluated as global functions after left-to-right argument
   evaluation. Every other non-special head is delegated, unchanged, to the
   opaque world relation [other]. *)
Definition fn_heads := [TRUEP; "CONSP"; "STRINGP"; "NUMBERP"; "NULL"; "NOT"; "EQ"; "EQUAL";
 ">"; ">="; "<"; "<="; "cons?"; "string?"; "number?"; "empty?"; "not"; EQUALP;
 "shen-cl.absequal"; "shen-cl.numeric-equal"; "shen-cl.greater?";
 "shen-cl.greater-than-or-equal-to?"; "shen-cl.less?"; "shen-cl.less-than-or-equal-to?"; "fail"].
Definition special_heads := ["QUOTE"; "IF"; "PROGN"; "LET"; "LET*"; "AND"; "OR"; "and"; "or"].
Definition is_fn h := mem h fn_heads.
Definition is_special h := mem h special_heads.

Section CL.
Variable St : Type.
(* BoolErr is the Shen Boolean-type error. Its diagnostic text (shen-cl.true?
   uses "boolean expected: not ~A", the |if| macro uses "~S is not a boolean")
   is deliberately quotiented; printer effects are a contract. *)
Inductive out := Ok (v : sv) (s : St) | Raise (x : sv) (s : St) | BoolErr (v : sv) (s : St).
Inductive outl := LOkL (vs : list sv) (s : St) | LAb (o : out).
Inductive bres := BOk (acc : binding) (s : St) | BAb (o : out).
Definition abrupt (o : out) : Prop := match o with Ok _ _ => False | _ => True end.
Variable prim : string -> list sv -> St -> out -> Prop.
Variable other : binding -> sv -> St -> out -> Prop.

Definition guard_result (v : sv) (s : St) : out :=
 if is_true v then Ok (VSym "T") s else if is_false v then Ok VNil s else BoolErr v s.
Definition apply_fn (f : string) (vs : list sv) (s : St) (o : out) : Prop :=
 if String.eqb f TRUEP then match vs with [v] => o = guard_result v s | _ => False end
 else prim f vs s o.
(* (|if| y 'true 'false) from Shen-CL's |and| and |or| macros. *)
Definition sbool (o : out) : out :=
 match o with Ok v s => if is_true v || is_false v then Ok v s else BoolErr v s | o => o end.

Inductive ev : binding -> sv -> St -> out -> Prop :=
| ev_nil e s : ev e VNil s (Ok VNil s)
| ev_str e x s : ev e (VStr x) s (Ok (VStr x) s)
| ev_num e x s : ev e (VNum x) s (Ok (VNum x) s)
| ev_obj e n s : ev e (VObj n) s (Ok (VObj n) s)
| ev_t e s : ev e (VSym "T") s (Ok (VSym "T") s)
| ev_lex e x v s : x <> "T" -> lookup x e = Some v -> ev e (VSym x) s (Ok v s)
| ev_glob e x s o : x <> "T" -> lookup x e = None -> other e (VSym x) s o -> ev e (VSym x) s o
| ev_quote e d s : ev e (f2 "QUOTE" d) s (Ok d s)
| ev_if_t e c a b s v s1 o : ev e c s (Ok v s1) -> v <> VNil -> ev e a s1 o -> ev e (f4 "IF" c a b) s o
| ev_if_f e c a b s s1 o : ev e c s (Ok VNil s1) -> ev e b s1 o -> ev e (f4 "IF" c a b) s o
| ev_if_x e c a b s o : ev e c s o -> abrupt o -> ev e (f4 "IF" c a b) s o
| ev_progn e fs s o : ev_seq e fs s o -> ev e (VCons (VSym "PROGN") fs) s o
| ev_let e bs body s acc s1 o : ev_binds false e [] bs s (BOk acc s1) -> ev_seq (app acc e) body s1 o ->
   ev e (VCons (VSym "LET") (VCons bs body)) s o
| ev_let_x e bs body s o : ev_binds false e [] bs s (BAb o) -> ev e (VCons (VSym "LET") (VCons bs body)) s o
| ev_lets e bs body s acc s1 o : ev_binds true e [] bs s (BOk acc s1) -> ev_seq (app acc e) body s1 o ->
   ev e (VCons (VSym "LET*") (VCons bs body)) s o
| ev_lets_x e bs body s o : ev_binds true e [] bs s (BAb o) -> ev e (VCons (VSym "LET*") (VCons bs body)) s o
| ev_and0 e s : ev e (VCons (VSym "AND") VNil) s (Ok (VSym "T") s)
| ev_and1 e a s o : ev e a s o -> ev e (f2 "AND" a) s o
| ev_and_t e a b r s v s1 o : ev e a s (Ok v s1) -> v <> VNil -> ev e (VCons (VSym "AND") (VCons b r)) s1 o ->
   ev e (VCons (VSym "AND") (VCons a (VCons b r))) s o
| ev_and_f e a b r s s1 : ev e a s (Ok VNil s1) -> ev e (VCons (VSym "AND") (VCons a (VCons b r))) s (Ok VNil s1)
| ev_and_x e a b r s o : ev e a s o -> abrupt o -> ev e (VCons (VSym "AND") (VCons a (VCons b r))) s o
| ev_or0 e s : ev e (VCons (VSym "OR") VNil) s (Ok VNil s)
| ev_or1 e a s o : ev e a s o -> ev e (f2 "OR" a) s o
| ev_or_t e a b r s v s1 : ev e a s (Ok v s1) -> v <> VNil -> ev e (VCons (VSym "OR") (VCons a (VCons b r))) s (Ok v s1)
| ev_or_f e a b r s s1 o : ev e a s (Ok VNil s1) -> ev e (VCons (VSym "OR") (VCons b r)) s1 o ->
   ev e (VCons (VSym "OR") (VCons a (VCons b r))) s o
| ev_or_x e a b r s o : ev e a s o -> abrupt o -> ev e (VCons (VSym "OR") (VCons a (VCons b r))) s o
| ev_sand_t e x y s s1 o : ev e x s (Ok (VSym "true") s1) -> ev e y s1 o -> ev e (f3 "and" x y) s (sbool o)
| ev_sand_f e x y s s1 : ev e x s (Ok (VSym "false") s1) -> ev e (f3 "and" x y) s (Ok (VSym "false") s1)
| ev_sand_b e x y s v s1 : ev e x s (Ok v s1) -> is_true v = false -> is_false v = false ->
   ev e (f3 "and" x y) s (BoolErr v s1)
| ev_sand_x e x y s o : ev e x s o -> abrupt o -> ev e (f3 "and" x y) s o
| ev_sor_t e x y s s1 : ev e x s (Ok (VSym "true") s1) -> ev e (f3 "or" x y) s (Ok (VSym "true") s1)
| ev_sor_f e x y s s1 o : ev e x s (Ok (VSym "false") s1) -> ev e y s1 o -> ev e (f3 "or" x y) s (sbool o)
| ev_sor_b e x y s v s1 : ev e x s (Ok v s1) -> is_true v = false -> is_false v = false ->
   ev e (f3 "or" x y) s (BoolErr v s1)
| ev_sor_x e x y s o : ev e x s o -> abrupt o -> ev e (f3 "or" x y) s o
| ev_call e f args s vs s1 o : is_fn f = true -> ev_list e args s (LOkL vs s1) -> apply_fn f vs s1 o ->
   ev e (VCons (VSym f) args) s o
| ev_call_x e f args s o : is_fn f = true -> ev_list e args s (LAb o) -> ev e (VCons (VSym f) args) s o
| ev_other e h args s o : is_fn h = false -> is_special h = false -> other e (VCons (VSym h) args) s o ->
   ev e (VCons (VSym h) args) s o
| ev_other_head e a args s o : (forall h, a <> VSym h) -> other e (VCons a args) s o -> ev e (VCons a args) s o
with ev_seq : binding -> sv -> St -> out -> Prop :=
| seq_nil e s : ev_seq e VNil s (Ok VNil s)
| seq_one e a s o : ev e a s o -> ev_seq e (VCons a VNil) s o
| seq_cons e a b r s v s1 o : ev e a s (Ok v s1) -> ev_seq e (VCons b r) s1 o -> ev_seq e (VCons a (VCons b r)) s o
| seq_x e a b r s o : ev e a s o -> abrupt o -> ev_seq e (VCons a (VCons b r)) s o
with ev_list : binding -> sv -> St -> outl -> Prop :=
| list_nil e s : ev_list e VNil s (LOkL [] s)
| list_cons e a r s v s1 vs s2 : ev e a s (Ok v s1) -> ev_list e r s1 (LOkL vs s2) ->
   ev_list e (VCons a r) s (LOkL (v :: vs) s2)
| list_x1 e a r s o : ev e a s o -> abrupt o -> ev_list e (VCons a r) s (LAb o)
| list_x2 e a r s v s1 o : ev e a s (Ok v s1) -> ev_list e r s1 (LAb o) -> ev_list e (VCons a r) s (LAb o)
with ev_binds : bool -> binding -> binding -> sv -> St -> bres -> Prop :=
| binds_nil k e acc s : ev_binds k e acc VNil s (BOk acc s)
| binds_cons (k : bool) (e acc : binding) x init r s v s1 res : x <> "T" -> ev (if k then app acc e else e) init s (Ok v s1) ->
   ev_binds k e ((x, v) :: acc) r s1 res -> ev_binds k e acc (VCons (VCons (VSym x) (VCons init VNil)) r) s res
| binds_x (k : bool) (e acc : binding) x init r s o : x <> "T" -> ev (if k then app acc e else e) init s o -> abrupt o ->
   ev_binds k e acc (VCons (VCons (VSym x) (VCons init VNil)) r) s (BAb o).

(* Observations of a value in test position. *)
Inductive tobs := TT (s : St) | TF (s : St) | TR (x : sv) (s : St) | TB (v : sv) (s : St).
Definition cl_test (o : out) : tobs :=
 match o with Ok v s => match v with VNil => TF s | _ => TT s end | Raise x s => TR x s | BoolErr v s => TB v s end.
Definition shen_test (o : out) : tobs :=
 match o with
 | Ok v s => if is_true v then TT s else if is_false v then TF s else TB v s
 | Raise x s => TR x s | BoolErr v s => TB v s end.
Definition Obs (test : out -> tobs) e x s t := exists o, ev e x s o /\ test o = t.
Definition CLT := Obs cl_test.
Definition SHT := Obs shen_test.
(* x may be replaced, in a CL test position, by y. *)
Definition OptEquiv x y := forall e s t, SHT e x s t <-> CLT e y s t.
Definition SeqEquiv xs ys := forall e s t,
 (exists o, ev_seq e xs s o /\ shen_test o = t) <-> (exists o, ev_seq e ys s o /\ cl_test o = t).

Lemma abrupt_tests : forall o, abrupt o -> shen_test o = cl_test o.
Proof. destruct o; simpl; tauto. Qed.
Lemma list_ab : forall e a s r, ev_list e a s r -> forall o, r = LAb o -> abrupt o.
Proof. intros e a s r H. induction H; intros o' Heq; try discriminate; injection Heq as <-; auto. Qed.
Lemma binds_ab : forall k e acc a s r, ev_binds k e acc a s r -> forall o, r = BAb o -> abrupt o.
Proof. intros k e acc a s r H. induction H; intros o' Heq; try discriminate; auto. injection Heq as <-; auto. Qed.

Ltac imposs := solve [ congruence
 | match goal with
   | H : is_fn _ = _ |- _ => vm_compute in H; discriminate H
   | H : is_special _ = _ |- _ => vm_compute in H; discriminate H
   | H : forall h, _ <> VSym h |- _ => exfalso; eapply H; reflexivity end ].

Lemma obs_if : forall test e c a b s t,
 Obs test e (f4 "IF" c a b) s t <->
 (exists v s1, ev e c s (Ok v s1) /\ v <> VNil /\ Obs test e a s1 t) \/
 (exists s1, ev e c s (Ok VNil s1) /\ Obs test e b s1 t) \/
 (exists o, ev e c s o /\ abrupt o /\ test o = t).
Proof.
 unfold Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + left. eauto 8.
   + right; left. eauto 8.
   + right; right. eauto 8.
 - intros [[v [s1 [Hc [Hv [o [Ha Ht]]]]]]|[[s1 [Hc [o [Hb Ht]]]]|[o [Hc [Hx Ht]]]]];
   exists o; split; auto; [eapply ev_if_t | eapply ev_if_f | eapply ev_if_x]; eauto.
Qed.

Lemma obs_cl_if : forall e c a b s o,
 ev e (f4 "IF" c a b) s o <->
 (exists s1, CLT e c s (TT s1) /\ ev e a s1 o) \/ (exists s1, CLT e c s (TF s1) /\ ev e b s1 o) \/
 (exists x s1, CLT e c s (TR x s1) /\ o = Raise x s1) \/ (exists v s1, CLT e c s (TB v s1) /\ o = BoolErr v s1).
Proof.
 unfold CLT, Obs. split.
 - intros H. inversion H; subst; try imposs.
   + left. exists s1. split; auto. exists (Ok v s1). split; auto. destruct v; simpl; congruence.
   + right; left. exists s1. split; auto. exists (Ok VNil s1). auto.
   + destruct o; simpl in *; try tauto.
     * right; right; left. exists x, s0. split; auto. exists (Raise x s0). auto.
     * right; right; right. exists v, s0. split; auto. exists (BoolErr v s0). auto.
 - intros [[s1 [[o0 [Hc Ht]] Ha]]|[[s1 [[o0 [Hc Ht]] Hb]]|[[x [s1 [[o0 [Hc Ht]] ->]]]|[v [s1 [[o0 [Hc Ht]] ->]]]]]].
   + destruct o0 as [v s2|x s2|v s2]; simpl in Ht; [destruct v|..]; try discriminate;
     injection Ht as <-; eapply ev_if_t; eauto; discriminate.
   + destruct o0 as [v s2|x s2|v s2]; simpl in Ht; [destruct v|..]; try discriminate.
     injection Ht as <-. eapply ev_if_f; eauto.
   + destruct o0 as [v s2|x' s2|v s2]; simpl in Ht; [destruct v|..]; try discriminate.
     injection Ht as <- <-. eapply ev_if_x; eauto. exact I.
   + destruct o0 as [v' s2|x s2|v' s2]; simpl in Ht; [destruct v'|..]; try discriminate.
     injection Ht as <- <-. eapply ev_if_x; eauto. exact I.
Qed.

Lemma seq_one_iff : forall e a s o, ev_seq e (VCons a VNil) s o <-> ev e a s o.
Proof. split; intros H; [inversion H; subst; auto | constructor; auto]. Qed.
Lemma seq_cons_iff : forall e a b r s o, ev_seq e (VCons a (VCons b r)) s o <->
 (exists v s1, ev e a s (Ok v s1) /\ ev_seq e (VCons b r) s1 o) \/ (ev e a s o /\ abrupt o).
Proof.
 split.
 - intros H; inversion H; subst; eauto.
 - intros [[v [s1 [Ha Hr]]]|[Ha Hx]]; [eapply seq_cons | eapply seq_x]; eauto.
Qed.

Lemma obs_progn : forall test e fs s t,
 Obs test e (VCons (VSym "PROGN") fs) s t <-> exists o, ev_seq e fs s o /\ test o = t.
Proof.
 unfold Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs. eauto.
 - intros [o [H Ht]]. exists o. split; auto. constructor; auto.
Qed.

Lemma obs_let : forall test (k : bool) e bs body s t,
 Obs test e (f3 (if k then "LET*" else "LET") bs body) s t <->
 (exists acc s1, ev_binds k e [] bs s (BOk acc s1) /\ Obs test (app acc e) body s1 t) \/
 (exists o, ev_binds k e [] bs s (BAb o) /\ test o = t).
Proof.
 unfold Obs. intros. split.
 - intros [o [H Ht]]. destruct k; inversion H; subst; try imposs;
   solve [left; exists acc, s1; split; auto; exists o; split; auto; apply seq_one_iff; auto | right; eauto].
 - intros [[acc [s1 [Hb [o [Hev Ht]]]]]|[o [Hb Ht]]]; exists o; split; auto; destruct k;
   solve [eapply ev_lets; eauto; apply seq_one_iff; auto | eapply ev_let; eauto; apply seq_one_iff; auto
         | eapply ev_lets_x; eauto | eapply ev_let_x; eauto].
Qed.

Lemma obs_call : forall test e f args s t, is_fn f = true ->
 (Obs test e (VCons (VSym f) args) s t <->
  (exists vs s1 o, ev_list e args s (LOkL vs s1) /\ apply_fn f vs s1 o /\ test o = t) \/
  (exists o, ev_list e args s (LAb o) /\ test o = t)).
Proof.
 unfold Obs. intros test e f args s t Hf. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + left. eauto 6.
   + right. eauto.
 - intros [[vs [s1 [o [Hl [Ha Ht]]]]]|[o [Hl Ht]]]; exists o; split; auto;
   [eapply ev_call | eapply ev_call_x]; eauto.
Qed.

Lemma list0_iff : forall e s r, ev_list e VNil s r <-> r = LOkL [] s.
Proof. split; intros H; [inversion H; auto | subst; constructor]. Qed.
Lemma list1_iff : forall e a s r, ev_list e (VCons a VNil) s r <->
 (exists v s1, ev e a s (Ok v s1) /\ r = LOkL [v] s1) \/ (exists o, ev e a s o /\ abrupt o /\ r = LAb o).
Proof.
 split.
 - intros H. inversion H; subst;
   try match goal with Hn : ev_list _ VNil _ _ |- _ => apply list0_iff in Hn end;
   try discriminate; eauto.
   match goal with Hn : LOkL _ _ = LOkL _ _ |- _ => injection Hn; intros; subst end. eauto.
 - intros [[v [s1 [Ha ->]]]|[o [Ha [Hx ->]]]]; [eapply list_cons | eapply list_x1]; eauto; constructor.
Qed.
Lemma list2_iff : forall e a b s r, ev_list e (VCons a (VCons b VNil)) s r <->
 (exists v s1 w s2, ev e a s (Ok v s1) /\ ev e b s1 (Ok w s2) /\ r = LOkL [v; w] s2) \/
 (exists o, ev e a s o /\ abrupt o /\ r = LAb o) \/
 (exists v s1 o, ev e a s (Ok v s1) /\ ev e b s1 o /\ abrupt o /\ r = LAb o).
Proof.
 split.
 - intros H. inversion H; subst;
   try match goal with Hn : ev_list _ (VCons _ VNil) _ _ |- _ =>
     apply list1_iff in Hn as [[w [s3 [Hb Heq]]]|[o' [Hb [Hx Heq]]]] end;
   try discriminate.
   + injection Heq; intros; subst. left. eauto 8.
   + right; left. eauto.
   + injection Heq; intros; subst. right; right. eauto 8.
 - intros [[v [s1 [w [s2 [Ha [Hb ->]]]]]]|[[o [Ha [Hx ->]]]|[v [s1 [o [Ha [Hb [Hx ->]]]]]]]].
   + eapply list_cons; eauto. apply list1_iff. eauto.
   + eapply list_x1; eauto.
   + eapply list_x2; eauto. apply list1_iff. eauto.
Qed.

Definition pure_lit (a d : sv) := forall e s o, ev e a s o <-> o = Ok d s.
Lemma pure_quote : forall d, pure_lit (f2 "QUOTE" d) d.
Proof. split; intros H; [inversion H; subst; try imposs; auto | subst; constructor]. Qed.
Lemma pure_num : forall n, pure_lit (VNum n) (VNum n).
Proof. split; intros H; [inversion H; auto | subst; constructor]. Qed.
Lemma pure_str : forall x, pure_lit (VStr x) (VStr x).
Proof. split; intros H; [inversion H; auto | subst; constructor]. Qed.

Lemma list_pure_right : forall e x a d s r, pure_lit a d -> (ev_list e (VCons x (VCons a VNil)) s r <->
 (exists v s1, ev e x s (Ok v s1) /\ r = LOkL [v; d] s1) \/ (exists o, ev e x s o /\ abrupt o /\ r = LAb o)).
Proof.
 intros e x a d s r Hp. rewrite list2_iff. split.
 - intros [[v [s1 [w [s2 [Ha [Hb ->]]]]]]|[[o [Ha [Hx ->]]]|[v [s1 [o [Ha [Hb [Hx ->]]]]]]]].
   + apply Hp in Hb. injection Hb as <- <-. eauto.
   + eauto.
   + apply Hp in Hb. subst. contradiction.
 - intros [[v [s1 [Ha ->]]]|[o [Ha [Hx ->]]]].
   + left. exists v, s1, d, s1. repeat split; auto. apply Hp. reflexivity.
   + right; left. eauto.
Qed.
Lemma list_pure_left : forall e x a d s r, pure_lit a d -> (ev_list e (VCons a (VCons x VNil)) s r <->
 (exists v s1, ev e x s (Ok v s1) /\ r = LOkL [d; v] s1) \/ (exists o, ev e x s o /\ abrupt o /\ r = LAb o)).
Proof.
 intros e x a d s r Hp. rewrite list2_iff. split.
 - intros [[v [s1 [w [s2 [Ha [Hb ->]]]]]]|[[o [Ha [Hx ->]]]|[v [s1 [o [Ha [Hb [Hx ->]]]]]]]].
   + apply Hp in Ha. injection Ha as <- <-. eauto.
   + apply Hp in Ha. subst. contradiction.
   + apply Hp in Ha. injection Ha as <- <-. right. eauto.
 - intros [[v [s1 [Hx ->]]]|[o [Hx [Hab ->]]]].
   + left. exists d, s, v, s1. repeat split; auto. apply Hp. reflexivity.
   + right; right. exists d, s, o. repeat split; auto. apply Hp. reflexivity.
Qed.

Lemma apply_fn_prim : forall f vs s o, f <> TRUEP -> (apply_fn f vs s o <-> prim f vs s o).
Proof. intros. unfold apply_fn. apply String.eqb_neq in H. rewrite H. tauto. Qed.

(* ----- Per-clause semantic facts ----- *)

Lemma sem_true : forall x, OptEquiv x (f2 TRUEP x).
Proof.
 intros x e s t. unfold CLT. rewrite obs_call by reflexivity. unfold SHT, Obs. split.
 - intros [o [H Ht]]. destruct o as [v s1|x' s1|v s1].
   + left. exists [v], s1, (guard_result v s1). split; [|split; [reflexivity|]].
     * apply list1_iff. eauto.
     * subst. unfold guard_result, shen_test. destruct (is_true v), (is_false v); reflexivity.
   + right. exists (Raise x' s1). split; auto. apply list1_iff. right. exists (Raise x' s1). repeat split; auto.
   + right. exists (BoolErr v s1). split; auto. apply list1_iff. right. exists (BoolErr v s1). repeat split; auto.
 - intros [[vs [s1 [o [Hl [Ha Ht]]]]]|[o [Hl Ht]]].
   + apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o' [_ [_ Heq]]]]; try discriminate.
     injection Heq; intros; subst. unfold apply_fn, TRUEP in Ha. simpl in Ha. subst o. exists (Ok v s2). split; auto.
     unfold guard_result, shen_test. destruct (is_true v), (is_false v); reflexivity.
   + apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o' [Hx [Hab Heq]]]]; try discriminate.
     injection Heq as <-. exists o. split; auto. rewrite abrupt_tests; auto.
Qed.

Lemma sem_if_tf : forall c, OptEquiv (f4 "IF" c (f2 "QUOTE" (VSym "true")) (f2 "QUOTE" (VSym "false"))) c.
Proof.
 intros c e s t. unfold SHT. rewrite obs_if. unfold CLT, Obs. split.
 - intros [[v [s1 [Hc [Hv [o [Ha Ht]]]]]]|[[s1 [Hc [o [Hb Ht]]]]|[o [Hc [Hx Ht]]]]].
   + apply pure_quote in Ha. subst. exists (Ok v s1). split; auto. destruct v; simpl; congruence.
   + apply pure_quote in Hb. subst. exists (Ok VNil s1). auto.
   + exists o. split; auto. rewrite <- abrupt_tests; auto.
 - intros [o [Hc Ht]]. destruct o as [v s1|x s1|v s1].
   + destruct (match v with VNil => true | _ => false end) eqn:Hn.
     * destruct v; try discriminate. right; left. exists s1. split; auto.
       exists (Ok (VSym "false") s1). split; [constructor | simpl in *; auto].
     * left. exists v, s1. split; auto. split; [intro; subst; discriminate|].
       exists (Ok (VSym "true") s1). split; [constructor|].
       destruct v; try discriminate; simpl in *; auto.
   + right; right. exists (Raise x s1). repeat split; auto.
   + right; right. exists (BoolErr v s1). repeat split; auto.
Qed.

Lemma sem_ifb : forall c a b a' b', OptEquiv a a' -> OptEquiv b b' -> OptEquiv (f4 "IF" c a b) (f4 "IF" c a' b').
Proof.
 intros c a b a' b' Ha Hb e s t. unfold SHT, CLT. rewrite !obs_if.
 split; intros [[v [s1 [Hc [Hv H]]]]|[[s1 [Hc H]]|[o [Hc [Hx Ht]]]]].
 - left. exists v, s1. repeat split; auto. apply Ha. exact H.
 - right; left. exists s1. split; auto. apply Hb. exact H.
 - right; right. exists o. repeat split; auto. rewrite <- abrupt_tests; auto.
 - left. exists v, s1. repeat split; auto. apply Ha. exact H.
 - right; left. exists s1. split; auto. apply Hb. exact H.
 - right; right. exists o. repeat split; auto. rewrite abrupt_tests; auto.
Qed.

Lemma sem_let : forall (k : bool) bs b b', OptEquiv b b' ->
 OptEquiv (f3 (if k then "LET*" else "LET") bs b) (f3 (if k then "LET*" else "LET") bs b').
Proof.
 intros k bs b b' Hb e s t. unfold SHT, CLT. rewrite !obs_let.
 split; intros [[acc [s1 [Hbs H]]]|[o [Hbs Ht]]].
 - left. exists acc, s1. split; auto. apply Hb. exact H.
 - right. exists o. split; auto. rewrite <- abrupt_tests; eauto using binds_ab.
 - left. exists acc, s1. split; auto. apply Hb. exact H.
 - right. exists o. split; auto. rewrite abrupt_tests; eauto using binds_ab.
Qed.

Lemma sem_progn : forall fs fs', SeqEquiv fs fs' -> OptEquiv (VCons (VSym "PROGN") fs) (VCons (VSym "PROGN") fs').
Proof. intros fs fs' H e s t. unfold SHT, CLT. rewrite !obs_progn. apply H. Qed.
Lemma sem_seq_one : forall l l', OptEquiv l l' -> SeqEquiv (VCons l VNil) (VCons l' VNil).
Proof.
 intros l l' H e s t. split; intros [o [Hs Ht]]; apply seq_one_iff in Hs.
 - destruct (proj1 (H e s t) (ex_intro _ o (conj Hs Ht))) as [o' [? ?]]. exists o'. split; auto. apply seq_one_iff; auto.
 - destruct (proj2 (H e s t) (ex_intro _ o (conj Hs Ht))) as [o' [? ?]]. exists o'. split; auto. apply seq_one_iff; auto.
Qed.
Lemma sem_seq_cons : forall f b r b' r', SeqEquiv (VCons b r) (VCons b' r') ->
 SeqEquiv (VCons f (VCons b r)) (VCons f (VCons b' r')).
Proof.
 intros f b r b' r' H e s t. split; intros [o [Hs Ht]]; apply seq_cons_iff in Hs as [[v [s1 [Hf Hr]]]|[Hf Hx]].
 - destruct (proj1 (H e s1 t) (ex_intro _ o (conj Hr Ht))) as [o' [? ?]]. exists o'. split; auto.
   apply seq_cons_iff. eauto.
 - exists o. split; [apply seq_cons_iff; auto | rewrite <- abrupt_tests; auto].
 - destruct (proj2 (H e s1 t) (ex_intro _ o (conj Hr Ht))) as [o' [? ?]]. exists o'. split; auto.
   apply seq_cons_iff. eauto.
 - exists o. split; [apply seq_cons_iff; auto | rewrite abrupt_tests; auto].
Qed.

Lemma sem_quote_true : OptEquiv (f2 "QUOTE" (VSym "true")) (VSym "T").
Proof.
 intros e s t. unfold SHT, CLT, Obs. split; intros [o [H Ht]].
 - apply pure_quote in H. subst. exists (Ok (VSym "T") s). split; [constructor | reflexivity].
 - inversion H; subst; try congruence. exists (Ok (VSym "true") s). split; [constructor | reflexivity].
Qed.
Lemma sem_quote_false : OptEquiv (f2 "QUOTE" (VSym "false")) VNil.
Proof.
 intros e s t. unfold SHT, CLT, Obs. split; intros [o [H Ht]].
 - apply pure_quote in H. subst. exists (Ok VNil s). split; [constructor | reflexivity].
 - inversion H; subst. exists (Ok (VSym "false") s). split; [constructor | reflexivity].
Qed.

Definition args_refine f xs g ys := forall s t,
 (exists o, prim f xs s o /\ shen_test o = t) <-> (exists o, prim g ys s o /\ cl_test o = t).
Definition pred_refines f g := forall vs, args_refine f vs g vs.

Lemma sem_call : forall f g a1 a2, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 (forall e s o, ev_list e a1 s (LAb o) <-> ev_list e a2 s (LAb o)) ->
 (forall e s t, (exists vs s1 o, ev_list e a1 s (LOkL vs s1) /\ prim f vs s1 o /\ shen_test o = t) <->
                (exists vs s1 o, ev_list e a2 s (LOkL vs s1) /\ prim g vs s1 o /\ cl_test o = t)) ->
 OptEquiv (VCons (VSym f) a1) (VCons (VSym g) a2).
Proof.
 intros f g a1 a2 Hf Hg Nf Ng Hab Hok e s t. unfold SHT, CLT. rewrite !obs_call by assumption.
 split; intros [[vs [s1 [o [Hl [Ha Ht]]]]]|[o [Hl Ht]]].
 - left. apply apply_fn_prim in Ha; auto.
   destruct (proj1 (Hok e s t) (ex_intro _ vs (ex_intro _ s1 (ex_intro _ o (conj Hl (conj Ha Ht))))))
     as [vs' [s1' [o' [? [? ?]]]]].
   exists vs', s1', o'. repeat split; auto. apply apply_fn_prim; auto.
 - right. exists o. split; [apply Hab; auto|]. rewrite <- abrupt_tests; eauto using list_ab.
 - left. apply apply_fn_prim in Ha; auto.
   destruct (proj2 (Hok e s t) (ex_intro _ vs (ex_intro _ s1 (ex_intro _ o (conj Hl (conj Ha Ht))))))
     as [vs' [s1' [o' [? [? ?]]]]].
   exists vs', s1', o'. repeat split; auto. apply apply_fn_prim; auto.
 - right. exists o. split; [apply Hab; auto|]. rewrite abrupt_tests; eauto using list_ab.
Qed.

Lemma sem_same_args : forall f g args, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 (forall e s vs s1, ev_list e args s (LOkL vs s1) -> args_refine f vs g vs) ->
 OptEquiv (VCons (VSym f) args) (VCons (VSym g) args).
Proof.
 intros f g args Hf Hg Nf Ng H. apply sem_call; auto; [tauto|]. intros e s t. split.
 - intros [vs [s1 [o [Hl [Hp Ht]]]]].
   destruct (proj1 (H e s vs s1 Hl s1 t) (ex_intro _ o (conj Hp Ht))) as [o' [? ?]]. eauto 7.
 - intros [vs [s1 [o [Hl [Hp Ht]]]]].
   destruct (proj2 (H e s vs s1 Hl s1 t) (ex_intro _ o (conj Hp Ht))) as [o' [? ?]]. eauto 7.
Qed.

Lemma sem_pred : forall f g args, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 pred_refines f g -> OptEquiv (VCons (VSym f) args) (VCons (VSym g) args).
Proof. intros. apply sem_same_args; auto. Qed.

(* The optimizer only ever emits a predicate with the argument count its
   source pattern fixed: [cons? X] has one operand, [greater? X Y] two. The
   refinement is therefore needed at exactly that arity. *)
Lemma sem_pred1 : forall f g x, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 (forall v, args_refine f [v] g [v]) -> OptEquiv (f2 f x) (f2 g x).
Proof.
 intros f g x Hf Hg Nf Ng H. apply sem_same_args; auto. intros e s vs s1 Hl.
 apply list1_iff in Hl as [[v [s2 [_ Heq]]]|[o [_ [_ Heq]]]]; try discriminate.
 injection Heq; intros; subst. apply H.
Qed.
Lemma sem_pred2 : forall f g x y, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 (forall v w, args_refine f [v; w] g [v; w]) -> OptEquiv (f3 f x y) (f3 g x y).
Proof.
 intros f g x y Hf Hg Nf Ng H. apply sem_same_args; auto. intros e s vs s1 Hl.
 apply list2_iff in Hl as [[v [s2 [w [s3 [_ [_ Heq]]]]]]|[[o [_ [_ Heq]]]|[? [? [o [_ [_ [_ Heq]]]]]]]];
 try discriminate. injection Heq; intros; subst. apply H.
Qed.
(* Every instance of the former all-arity field is an instance of the
   narrowed one, so narrowing only enlarges the set of admissible worlds. *)
Lemma pred_refines_narrows : forall f g, pred_refines f g ->
 (forall v, args_refine f [v] g [v]) /\ (forall v w, args_refine f [v; w] g [v; w]).
Proof. intros f g H. split; intros; apply H. Qed.

(* Two argument lists whose successful evaluations produce related value lists
   and whose abrupt evaluations coincide. *)
Lemma sem_args_map : forall f g a1 a2 (m : list sv -> list sv), is_fn f = true -> is_fn g = true ->
 f <> TRUEP -> g <> TRUEP ->
 (forall e s o, ev_list e a1 s (LAb o) <-> ev_list e a2 s (LAb o)) ->
 (forall e s vs s1, ev_list e a1 s (LOkL vs s1) <-> exists ws, ev_list e a2 s (LOkL ws s1) /\ vs = m ws) ->
 (forall e s ws s1, ev_list e a2 s (LOkL ws s1) -> args_refine f (m ws) g ws) ->
 OptEquiv (VCons (VSym f) a1) (VCons (VSym g) a2).
Proof.
 intros f g a1 a2 m Hf Hg Nf Ng Hab Hmap Href. apply sem_call; auto. intros e s t. split.
 - intros [vs [s1 [o [Hl [Hp Ht]]]]]. apply Hmap in Hl as [ws [Hl' ->]].
   destruct (proj1 (Href e s ws s1 Hl' s1 t) (ex_intro _ o (conj Hp Ht))) as [o' [? ?]]. eauto 7.
 - intros [ws [s1 [o [Hl [Hp Ht]]]]].
   destruct (proj2 (Href e s ws s1 Hl s1 t) (ex_intro _ o (conj Hp Ht))) as [o' [? ?]].
   exists (m ws), s1, o'. repeat split; auto. apply Hmap. eauto.
Qed.

(* ----- Shen and/or/not and CL AND/OR/NOT ----- *)
Definition not_tt (t : tobs) := match t with TT _ => False | _ => True end.
Definition not_tf (t : tobs) := match t with TF _ => False | _ => True end.
Definition neg (t : tobs) := match t with TT s => TF s | TF s => TT s | t => t end.

Lemma shen_test_sbool : forall o, shen_test (sbool o) = shen_test o.
Proof.
 destruct o; simpl; auto. destruct (is_true v) eqn:T; destruct (is_false v) eqn:F; simpl; rewrite ?T, ?F; auto.
Qed.
Lemma sht_true : forall e x s s1, SHT e x s (TT s1) <-> ev e x s (Ok (VSym "true") s1).
Proof.
 unfold SHT, Obs. split.
 - intros [o [H Ht]]. destruct o as [v s2|x' s2|v s2]; simpl in Ht; try discriminate.
   destruct (is_true v) eqn:T; [|destruct (is_false v); discriminate].
   injection Ht as <-. apply sv_eqb_eq in T. subst. auto.
 - intros H. exists (Ok (VSym "true") s1). auto.
Qed.
Lemma sht_false : forall e x s s1, SHT e x s (TF s1) <-> ev e x s (Ok (VSym "false") s1).
Proof.
 unfold SHT, Obs. split.
 - intros [o [H Ht]]. destruct o as [v s2|x' s2|v s2]; simpl in Ht; try discriminate.
   destruct (is_true v) eqn:T; [discriminate|]. destruct (is_false v) eqn:F; [|discriminate].
   injection Ht as <-. apply sv_eqb_eq in F. subst. auto.
 - intros H. exists (Ok (VSym "false") s1). auto.
Qed.

Lemma obs_sand : forall e x y s t, SHT e (f3 "and" x y) s t <->
 (exists s1, SHT e x s (TT s1) /\ SHT e y s1 t) \/ (SHT e x s t /\ not_tt t).
Proof.
 intros. unfold SHT at 1, Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + left. exists s1. split; [apply sht_true; auto|]. exists o0. split; auto. symmetry. apply shen_test_sbool.
   + right. split; [apply sht_false; auto | exact I].
   + right. split; [exists (Ok v s1); split; auto; simpl; match goal with T : is_true v = false, F : is_false v = false |- _ => rewrite T, F; auto end | exact I].
   + right. split; [exists o; auto|]. destruct o; simpl in *; tauto.
 - intros [[s1 [Hx [o [Hy Ht]]]]|[[o [Hx Ht]] Hn]].
   + exists (sbool o). split; [eapply ev_sand_t; eauto; apply sht_true; auto | rewrite shen_test_sbool; auto].
   + destruct o as [v s1|x' s1|v s1].
     * simpl in Ht. destruct (is_true v) eqn:T; [subst; contradiction|].
       destruct (is_false v) eqn:F.
       -- apply sv_eqb_eq in F. subst. exists (Ok (VSym "false") s1). split; [apply ev_sand_f; auto | reflexivity].
       -- exists (BoolErr v s1). split; [apply ev_sand_b; auto | subst; reflexivity].
     * exists (Raise x' s1). split; auto. apply ev_sand_x; auto. exact I.
     * exists (BoolErr v s1). split; auto. apply ev_sand_x; auto. exact I.
Qed.

Lemma obs_sor : forall e x y s t, SHT e (f3 "or" x y) s t <->
 (exists s1, SHT e x s (TF s1) /\ SHT e y s1 t) \/ (SHT e x s t /\ not_tf t).
Proof.
 intros. unfold SHT at 1, Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + right. split; [apply sht_true; auto | exact I].
   + left. exists s1. split; [apply sht_false; auto|]. exists o0. split; auto. symmetry. apply shen_test_sbool.
   + right. split; [exists (Ok v s1); split; auto; simpl; match goal with T : is_true v = false, F : is_false v = false |- _ => rewrite T, F; auto end | exact I].
   + right. split; [exists o; auto|]. destruct o; simpl in *; tauto.
 - intros [[s1 [Hx [o [Hy Ht]]]]|[[o [Hx Ht]] Hn]].
   + exists (sbool o). split; [eapply ev_sor_f; eauto; apply sht_false; auto | rewrite shen_test_sbool; auto].
   + destruct o as [v s1|x' s1|v s1].
     * simpl in Ht. destruct (is_true v) eqn:T.
       -- apply sv_eqb_eq in T. subst. exists (Ok (VSym "true") s1). split; [apply ev_sor_t; auto | reflexivity].
       -- destruct (is_false v) eqn:F; [subst; contradiction|].
          exists (BoolErr v s1). split; [apply ev_sor_b; auto | subst; reflexivity].
     * exists (Raise x' s1). split; auto. apply ev_sor_x; auto. exact I.
     * exists (BoolErr v s1). split; auto. apply ev_sor_x; auto. exact I.
Qed.

Lemma clt_tt : forall e x s s1, CLT e x s (TT s1) <-> exists v, ev e x s (Ok v s1) /\ v <> VNil.
Proof.
 unfold CLT, Obs. split.
 - intros [o [H Ht]]. destruct o as [v s2|x' s2|v s2]; simpl in Ht; [destruct v|..]; try discriminate;
   injection Ht as <-; eexists; split; eauto; discriminate.
 - intros [v [H Hv]]. exists (Ok v s1). split; auto. destruct v; simpl; congruence.
Qed.
Lemma clt_tf : forall e x s s1, CLT e x s (TF s1) <-> ev e x s (Ok VNil s1).
Proof.
 unfold CLT, Obs. split.
 - intros [o [H Ht]]. destruct o as [v s2|x' s2|v s2]; simpl in Ht; [destruct v|..]; try discriminate.
   injection Ht as <-. auto.
 - intros H. exists (Ok VNil s1). auto.
Qed.

Lemma obs_cand : forall e x y s t, CLT e (f3 "AND" x y) s t <->
 (exists s1, CLT e x s (TT s1) /\ CLT e y s1 t) \/ (CLT e x s t /\ not_tt t).
Proof.
 intros. unfold CLT at 1, Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + left. exists s1. split; [apply clt_tt; eauto|].
     match goal with Hi : ev _ (VCons (VSym _) (VCons _ VNil)) _ _ |- _ => inversion Hi; subst; try imposs end. exists o. auto.
   + right. split; [apply clt_tf; auto | exact I].
   + right. split; [exists o; auto|]. destruct o; simpl in *; tauto.
 - intros [[s1 [Hx [o [Hy Ht]]]]|[[o [Hx Ht]] Hn]].
   + apply clt_tt in Hx as [v [Hx Hv]]. exists o. split; auto. eapply ev_and_t; eauto. apply ev_and1. auto.
   + destruct o as [v s1|x' s1|v s1].
     * destruct v; simpl in Ht; subst; try contradiction.
       exists (Ok VNil s1). split; [apply ev_and_f; auto | reflexivity].
     * exists (Raise x' s1). split; auto. apply ev_and_x; auto. exact I.
     * exists (BoolErr v s1). split; auto. apply ev_and_x; auto. exact I.
Qed.

Lemma obs_cor : forall e x y s t, CLT e (f3 "OR" x y) s t <->
 (exists s1, CLT e x s (TF s1) /\ CLT e y s1 t) \/ (CLT e x s t /\ not_tf t).
Proof.
 intros. unfold CLT at 1, Obs. split.
 - intros [o [H Ht]]. inversion H; subst; try imposs.
   + right. split; [exists (Ok v s1); auto | destruct v; simpl; auto; congruence].
   + left. exists s1. split; [apply clt_tf; auto|].
     match goal with Hi : ev _ (VCons (VSym _) (VCons _ VNil)) _ _ |- _ => inversion Hi; subst; try imposs end. exists o. auto.
   + right. split; [exists o; auto|]. destruct o; simpl in *; tauto.
 - intros [[s1 [Hx [o [Hy Ht]]]]|[[o [Hx Ht]] Hn]].
   + apply clt_tf in Hx. exists o. split; auto. eapply ev_or_f; eauto. apply ev_or1. auto.
   + destruct o as [v s1|x' s1|v s1].
     * exists (Ok v s1). split; [apply ev_or_t; auto; intro Hv0; subst v; simpl in Ht; subst t; contradiction | exact Ht].
     * exists (Raise x' s1). split; auto. apply ev_or_x; auto. exact I.
     * exists (BoolErr v s1). split; auto. apply ev_or_x; auto. exact I.
Qed.

Lemma sem_and : forall p q p' q', OptEquiv p p' -> OptEquiv q q' -> OptEquiv (f3 "and" p q) (f3 "AND" p' q').
Proof.
 intros p q p' q' Hp Hq e s t. rewrite obs_sand, obs_cand. split.
 - intros [[s1 [H1 H2]]|[H1 H2]]; [left; exists s1; split; [apply Hp|apply Hq]; auto | right; split; [apply Hp|]; auto].
 - intros [[s1 [H1 H2]]|[H1 H2]]; [left; exists s1; split; [apply Hp|apply Hq]; auto | right; split; [apply Hp|]; auto].
Qed.
Lemma sem_or : forall p q p' q', OptEquiv p p' -> OptEquiv q q' -> OptEquiv (f3 "or" p q) (f3 "OR" p' q').
Proof.
 intros p q p' q' Hp Hq e s t. rewrite obs_sor, obs_cor. split.
 - intros [[s1 [H1 H2]]|[H1 H2]]; [left; exists s1; split; [apply Hp|apply Hq]; auto | right; split; [apply Hp|]; auto].
 - intros [[s1 [H1 H2]]|[H1 H2]]; [left; exists s1; split; [apply Hp|apply Hq]; auto | right; split; [apply Hp|]; auto].
Qed.



Lemma obs_unary : forall test e f p s t (R : sv -> St -> out), is_fn f = true -> f <> TRUEP ->
 (forall v s o, prim f [v] s o <-> o = R v s) ->
 (Obs test e (f2 f p) s t <->
  (exists v s1, ev e p s (Ok v s1) /\ test (R v s1) = t) \/ (exists o, ev e p s o /\ abrupt o /\ test o = t)).
Proof.
 intros test e f p s t R Hf Nf HR. rewrite obs_call by assumption. split.
 - intros [[vs [s1 [o [Hl [Ha Ht]]]]]|[o [Hl Ht]]].
   + apply list1_iff in Hl as [[v [s2 [Hp Heq]]]|[o' [_ [_ Heq]]]]; try discriminate.
     injection Heq; intros; subst. apply apply_fn_prim in Ha; auto. apply HR in Ha. subst. left; eauto.
   + apply list1_iff in Hl as [[v [s2 [Hp Heq]]]|[o' [Hp [Hx Heq]]]]; try discriminate.
     injection Heq; intros; subst. right; eauto.
 - intros [[v [s1 [Hp Ht]]]|[o [Hp [Hx Ht]]]].
   + left. exists [v], s1, (R v s1). split; [apply list1_iff; eauto|]. split; auto.
     apply apply_fn_prim; auto. apply HR. reflexivity.
   + right. exists o. split; auto. apply list1_iff. right. eauto.
Qed.

Definition shen_not_result (v : sv) (s : St) : out :=
 if is_true v then Ok (VSym "false") s else if is_false v then Ok (VSym "true") s else BoolErr v s.
Definition cl_not_result (v : sv) (s : St) : out := Ok (match v with VNil => VSym "T" | _ => VNil end) s.

Lemma neg_obs : forall (O : St -> tobs -> Prop) (test : out -> tobs) e p s t (R : sv -> St -> out),
 (forall s t, O s t <-> Obs test e p s t) ->
 (forall v s1, test (R v s1) = neg (test (Ok v s1))) ->
 (forall o, abrupt o -> neg (test o) = test o) ->
 ((exists v s1, ev e p s (Ok v s1) /\ test (R v s1) = t) \/ (exists o, ev e p s o /\ abrupt o /\ test o = t))
 <-> exists t0, O s t0 /\ t = neg t0.
Proof.
 intros O test e p s t R HO HR Hab. split.
 - intros [[v [s1 [Hp Ht]]]|[o [Hp [Hx Ht]]]].
   + exists (test (Ok v s1)). split; [apply HO; exists (Ok v s1); auto | rewrite <- HR; congruence].
   + exists (test o). split; [apply HO; exists o; auto | rewrite Hab by auto; congruence].
 - intros [t0 [Ho ->]]. apply HO in Ho as [o [Hp Ht]]. destruct o as [v s1|x s1|v s1].
   + left. exists v, s1. split; auto. rewrite HR. subst. auto.
   + right. exists (Raise x s1). repeat split; auto. rewrite <- Ht, Hab; [reflexivity | exact I].
   + right. exists (BoolErr v s1). repeat split; auto. rewrite <- Ht, Hab; [reflexivity | exact I].
Qed.

Lemma sem_not : (forall v s o, prim "not" [v] s o <-> o = shen_not_result v s) ->
 (forall v s o, prim "NOT" [v] s o <-> o = cl_not_result v s) ->
 forall p p', OptEquiv p p' -> OptEquiv (f2 "not" p) (f2 "NOT" p').
Proof.
 intros Hn Hcn p p' Hp e s t. unfold SHT, CLT.
 rewrite (obs_unary shen_test e "not" p s t shen_not_result) by (reflexivity || discriminate || exact Hn).
 rewrite (obs_unary cl_test e "NOT" p' s t cl_not_result) by (reflexivity || discriminate || exact Hcn).
 rewrite (neg_obs (SHT e p) shen_test e p s t shen_not_result).
 2: { intros; reflexivity. }
 2: { intros v s1. unfold shen_not_result. simpl.
      destruct (is_true v) eqn:T; [apply sv_eqb_eq in T; subst; reflexivity|].
      destruct (is_false v) eqn:F; [apply sv_eqb_eq in F; subst; reflexivity|]. reflexivity. }
 2: { destruct o; simpl; tauto. }
 rewrite (neg_obs (CLT e p') cl_test e p' s t cl_not_result).
 2: { intros; reflexivity. }
 2: { intros v s1. destruct v; reflexivity. }
 2: { destruct o; simpl; tauto. }
 split; intros [t0 [H ->]]; exists t0; split; auto; apply Hp; auto.
Qed.

(* ----- Named primitive contracts (owned by E2E-17; hypotheses here) ----- *)
(* Each field is stated at exactly the arity and shape the captured
   optimise-boolean-check emits. An earlier version required the predicate
   fields for every argument list (pred_refines); a wrong-arity call of a
   wrapper is never emitted, and SBCL answers it with a fresh program-error
   naming the called function, so that form was a false requirement
   (CLContracts.all_arity_unjustified). pred_refines_narrows shows the old
   fields imply these. CLContracts.captured_contracts discharges the record
   for the world that runs the captured primitives.lsp bodies. *)
Record primitive_contracts : Prop := {
 pc_cons : forall v, args_refine "cons?" [v] "CONSP" [v];
 pc_string : forall v, args_refine "string?" [v] "STRINGP" [v];
 pc_number : forall v, args_refine "number?" [v] "NUMBERP" [v];
 pc_empty : forall v, args_refine "empty?" [v] "NULL" [v];
 pc_greater : forall v w, args_refine "shen-cl.greater?" [v; w] ">" [v; w];
 pc_greater_eq : forall v w, args_refine "shen-cl.greater-than-or-equal-to?" [v; w] ">=" [v; w];
 pc_less : forall v w, args_refine "shen-cl.less?" [v; w] "<" [v; w];
 pc_less_eq : forall v w, args_refine "shen-cl.less-than-or-equal-to?" [v; w] "<=" [v; w];
 pc_absequal : forall v w, args_refine EQUALP [v; w] "shen-cl.absequal" [v; w];
 pc_not : forall v s o, prim "not" [v] s o <-> o = shen_not_result v s;
 pc_cl_not : forall v s o, prim "NOT" [v] s o <-> o = cl_not_result v s;
 pc_null_right : forall v, args_refine EQUALP [v; VNil] "NULL" [v];
 pc_null_left : forall v, args_refine EQUALP [VNil; v] "NULL" [v];
 pc_fail : forall s a s1, prim "fail" [] s (Ok a s1) -> forall v,
   args_refine EQUALP [a; v] "EQ" [a; v] /\ args_refine EQUALP [v; a] "EQ" [v; a];
 pc_string_equal : forall x v,
   args_refine EQUALP [VStr x; v] "EQUAL" [VStr x; v] /\ args_refine EQUALP [v; VStr x] "EQUAL" [v; VStr x];
 pc_numeric : forall n v, args_refine EQUALP [v; VNum n] "shen-cl.numeric-equal" [v; VNum n]
   /\ args_refine EQUALP [VNum n; v] "shen-cl.numeric-equal" [v; VNum n];
 pc_symbol_eq : forall d v, symbolic d = true ->
   args_refine EQUALP [v; d] "EQ" [v; d] /\ args_refine EQUALP [d; v] "EQ" [v; d] }.

Hypothesis C : primitive_contracts.

Lemma sem_null_right : forall x, OptEquiv (f3 EQUALP x (f2 "QUOTE" VNil)) (f2 "NULL" x).
Proof.
 intros x. apply sem_args_map with (m := fun ws => match ws with [v] => [v; VNil] | _ => [] end);
 try reflexivity; try discriminate.
 - intros e s o. rewrite (list_pure_right e x _ VNil s) by apply pure_quote. rewrite list1_iff.
   split; intros [[? [? [? ?]]]|H]; try discriminate; right; exact H.
 - intros e s vs s1. rewrite (list_pure_right e x _ VNil s) by apply pure_quote. split.
   + intros [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate. injection Heq; intros; subst.
     exists [v]. split; auto. apply list1_iff. eauto.
   + intros [ws [Hl ->]]. apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate.
     injection Heq; intros; subst. left. eauto.
 - intros e s ws s1 Hl. apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate.
   injection Heq; intros; subst. apply (pc_null_right C).
Qed.

Lemma sem_null_left : forall x, OptEquiv (f3 EQUALP (f2 "QUOTE" VNil) x) (f2 "NULL" x).
Proof.
 intros x. apply sem_args_map with (m := fun ws => match ws with [v] => [VNil; v] | _ => [] end);
 try reflexivity; try discriminate.
 - intros e s o. rewrite (list_pure_left e x _ VNil s) by apply pure_quote. rewrite list1_iff.
   split; intros [[? [? [? ?]]]|H]; try discriminate; right; exact H.
 - intros e s vs s1. rewrite (list_pure_left e x _ VNil s) by apply pure_quote. split.
   + intros [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate. injection Heq; intros; subst.
     exists [v]. split; auto. apply list1_iff. eauto.
   + intros [ws [Hl ->]]. apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate.
     injection Heq; intros; subst. left. eauto.
 - intros e s ws s1 Hl. apply list1_iff in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate.
   injection Heq; intros; subst. apply (pc_null_left C).
Qed.

(* A literal operand moved across an arbitrary expression: the literal has no
   effect, so the left-to-right order of observable effects is unchanged. *)
Lemma sem_swap_lit : forall f g x a d, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 pure_lit a d -> (forall v, args_refine f [d; v] g [v; d]) ->
 OptEquiv (f3 f a x) (f3 g x a).
Proof.
 intros f g x a d Hf Hg Nf Ng Hp Hr.
 apply sem_args_map with (m := fun ws => match ws with [v; _] => [d; v] | _ => [] end); auto.
 - intros e s o. rewrite (list_pure_left e x a d s), (list_pure_right e x a d s) by exact Hp.
   split; intros [[? [? [? ?]]]|H]; try discriminate; right; exact H.
 - intros e s vs s1. rewrite (list_pure_left e x a d s) by exact Hp. split.
   + intros [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; try discriminate. injection Heq; intros; subst.
     exists [v; d]. split; auto. apply (list_pure_right e x a d s); auto. eauto.
   + intros [ws [Hl ->]]. apply (list_pure_right e x a d s) in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]];
     auto; try discriminate. injection Heq; intros; subst. left. eauto.
 - intros e s ws s1 Hl. apply (list_pure_right e x a d s) in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]];
   auto; try discriminate. injection Heq; intros; subst. apply Hr.
Qed.

Lemma sem_same2_lit_right : forall f g x a d, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 pure_lit a d -> (forall v, args_refine f [v; d] g [v; d]) -> OptEquiv (f3 f x a) (f3 g x a).
Proof.
 intros f g x a d Hf Hg Nf Ng Hp Hr. apply sem_same_args; auto. intros e s vs s1 Hl.
 apply (list_pure_right e x a d s) in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; auto; try discriminate.
 injection Heq; intros; subst. apply Hr.
Qed.
Lemma sem_same2_lit_left : forall f g x a d, is_fn f = true -> is_fn g = true -> f <> TRUEP -> g <> TRUEP ->
 pure_lit a d -> (forall v, args_refine f [d; v] g [d; v]) -> OptEquiv (f3 f a x) (f3 g a x).
Proof.
 intros f g x a d Hf Hg Nf Ng Hp Hr. apply sem_same_args; auto. intros e s vs s1 Hl.
 apply (list_pure_left e x a d s) in Hl as [[v [s2 [Hx Heq]]]|[o [_ [_ Heq]]]]; auto; try discriminate.
 injection Heq; intros; subst. apply Hr.
Qed.

Lemma fail_value : forall e s a s1, ev e (VCons (VSym "fail") VNil) s (Ok a s1) -> prim "fail" [] s (Ok a s1).
Proof.
 intros e s a s1 H. inversion H; subst; try imposs;
 match goal with Hl : ev_list _ VNil _ _ |- _ => apply list0_iff in Hl end; try discriminate.
 match goal with Hl : LOkL _ _ = LOkL _ _ |- _ => injection Hl; intros; subst end.
 match goal with Ha : apply_fn _ _ _ _ |- _ => apply apply_fn_prim in Ha; [exact Ha | discriminate] end.
Qed.

Lemma sem_fail_left : forall x,
 OptEquiv (f3 EQUALP (VCons (VSym "fail") VNil) x) (f3 "EQ" (VCons (VSym "fail") VNil) x).
Proof.
 intros x. apply sem_same_args; try reflexivity; try discriminate. intros e s vs s1 Hl.
 apply list2_iff in Hl as [[a [s2 [v [s3 [Ha [Hx Heq]]]]]]|[[o [_ [_ Heq]]]|[? [? [o [_ [_ [_ Heq]]]]]]]];
 try discriminate. injection Heq; intros; subst. apply fail_value in Ha. apply (pc_fail C _ _ _ Ha v).
Qed.
Lemma sem_fail_right : forall x,
 OptEquiv (f3 EQUALP x (VCons (VSym "fail") VNil)) (f3 "EQ" x (VCons (VSym "fail") VNil)).
Proof.
 intros x. apply sem_same_args; try reflexivity; try discriminate. intros e s vs s1 Hl.
 apply list2_iff in Hl as [[v [s2 [a [s3 [Hx [Ha Heq]]]]]]|[[o [_ [_ Heq]]]|[? [? [o [_ [_ [_ Heq]]]]]]]];
 try discriminate. injection Heq; intros; subst. apply fail_value in Ha. apply (pc_fail C _ _ _ Ha v).
Qed.


(* ----- The only input restriction: quoted comparands must be symbols ----- *)
(* optimise-boolean-check rewrites (shen-cl.equal? X 'S) to (EQ X 'S) for any
   quoted S. That agrees with Shen equality only when S is a symbol (or NIL);
   for a quoted cons, string, number or vector it does not. qsafe excludes
   such comparands anywhere in the input. *)
Definition quoted_ok (a : sv) : bool :=
 match a with VCons (VSym q) (VCons d VNil) => if String.eqb q "QUOTE" then symbolic d else true | _ => true end.
Definition qlocal (v : sv) : bool :=
 match v with
 | VCons (VSym f) (VCons a (VCons b VNil)) => if String.eqb f EQUALP then quoted_ok a && quoted_ok b else true
 | _ => true end.
Fixpoint qsafe (v : sv) : bool := match v with VCons a b => qlocal v && qsafe a && qsafe b | _ => true end.

Lemma qsafe_cons : forall a b, qsafe (VCons a b) = true -> qlocal (VCons a b) = true /\ qsafe a = true /\ qsafe b = true.
Proof. intros a b H. simpl in H. apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1]. auto. Qed.
Lemma qlocal_right : forall x d, qlocal (f3 EQUALP x (f2 "QUOTE" d)) = true -> symbolic d = true.
Proof. intros x d H. unfold qlocal, EQUALP in H. simpl in H. apply andb_true_iff in H. tauto. Qed.
Lemma qlocal_left : forall x d, qlocal (f3 EQUALP (f2 "QUOTE" d) x) = true -> symbolic d = true.
Proof. intros x d H. unfold qlocal, EQUALP in H. simpl in H. apply andb_true_iff in H. tauto. Qed.

Definition callf (n : nat) (ce : sv -> sv -> lres) : string -> list sv -> lres :=
 fun g vs => if String.eqb g CE then match vs with [a; b] => ce a b | _ => LUnsupported end
             else run n expected_defs ce g vs.
Lemma run_S : forall n ce f vals, run (S n) expected_defs ce f vals =
 match assoc f expected_defs with Some cs => apply_clauses (callf n ce) cs vals | None => LUnsupported end.
Proof. reflexivity. Qed.

Ltac no_match_inside x := lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end.
Ltac qsplit := repeat match goal with H : qsafe (VCons _ _) = true |- _ => apply qsafe_cons in H as [? [? ?]] end.

(* Matching a wildcard-free pattern reconstructs the input from the bindings. *)
Fixpoint fill (p : pat) (s : binding) : sv :=
 match p with
 | PVar x => match lookup x s with Some w => w | None => VNil end
 | PWild => VNil | PConst c => c | PCons a b => VCons (fill a s) (fill b s) end.
Fixpoint no_wild (p : pat) : bool := match p with PWild => false | PCons a b => no_wild a && no_wild b | _ => true end.
Fixpoint pvars (p : pat) : list string := match p with PVar x => [x] | PCons a b => app (pvars a) (pvars b) | _ => [] end.

Lemma match_pat_ext : forall p v s s', match_pat p v s = MOk s' ->
 forall x w, lookup x s = Some w -> lookup x s' = Some w.
Proof.
 induction p as [y| |c|p1 IH1 p2 IH2]; intros v s s' H x w Hx; simpl in H.
 - destruct (lookup y s) as [u|] eqn:E.
   + destruct (sv_eqb u v); [injection H as <-; auto | destruct (plain u && plain v); discriminate].
   + injection H as <-. simpl. destruct (String.eqb x y) eqn:E2; auto.
     apply String.eqb_eq in E2; subst. congruence.
 - injection H as <-; auto.
 - destruct (sv_eqb c v); [injection H as <-; auto | discriminate].
 - destruct v; try discriminate. destruct (match_pat p1 v1 s) eqn:E1; try discriminate. eauto.
Qed.
Lemma match_pat_bound : forall p v s s', match_pat p v s = MOk s' ->
 forall x, In x (pvars p) -> exists w, lookup x s' = Some w.
Proof.
 induction p as [y| |c|p1 IH1 p2 IH2]; intros v s s' H x Hin; simpl in *; try contradiction.
 - destruct Hin as [<-|[]]. destruct (lookup y s) as [u|] eqn:E.
   + destruct (sv_eqb u v); [injection H as <-; eauto | destruct (plain u && plain v); discriminate].
   + injection H as <-. simpl. rewrite String.eqb_refl. eauto.
 - destruct v; try discriminate. destruct (match_pat p1 v1 s) eqn:E1; try discriminate.
   apply in_app_or in Hin as [Hin|Hin].
   + destruct (IH1 _ _ _ E1 x Hin) as [w Hw]. exists w. eapply match_pat_ext; eauto.
   + eapply IH2; eauto.
Qed.
Lemma fill_ext : forall p s s', (forall x, In x (pvars p) -> exists w, lookup x s = Some w) ->
 (forall x w, lookup x s = Some w -> lookup x s' = Some w) -> fill p s = fill p s'.
Proof.
 induction p as [y| |c|p1 IH1 p2 IH2]; intros s s' Hb He; simpl in *; auto.
 - destruct (Hb y (or_introl eq_refl)) as [w Hw]. rewrite Hw, (He _ _ Hw). reflexivity.
 - rewrite (IH1 s s'), (IH2 s s'); auto; intros; apply Hb; apply in_or_app; auto.
Qed.
Lemma match_pat_fill : forall p v s s', match_pat p v s = MOk s' -> no_wild p = true -> v = fill p s'.
Proof.
 induction p as [y| |c|p1 IH1 p2 IH2]; intros v s s' H Hw; simpl in *.
 - destruct (lookup y s) as [u|] eqn:E.
   + destruct (sv_eqb u v) eqn:E2; [|destruct (plain u && plain v); discriminate].
     injection H as <-. apply sv_eqb_eq in E2. subst. rewrite E. reflexivity.
   + injection H as <-. simpl. rewrite String.eqb_refl. reflexivity.
 - discriminate.
 - destruct (sv_eqb c v) eqn:E; [|discriminate]. apply sv_eqb_eq in E. auto.
 - apply andb_true_iff in Hw as [Hw1 Hw2]. destruct v; try discriminate.
   destruct (match_pat p1 v1 s) eqn:E1; try discriminate.
   rewrite (IH1 _ _ _ E1 Hw1), (IH2 _ _ _ H Hw2). f_equal. apply fill_ext.
   + eapply match_pat_bound; eauto.
   + eapply match_pat_ext; eauto.
Qed.
Lemma match_pats1 : forall p v s, match_pats [p] [v] [] = MOk s -> match_pat p v [] = MOk s.
Proof. intros p v s H. simpl in H. destruct (match_pat p v []); congruence. Qed.

(* Destruct only binding lookups and Booleans: no case split on input data. *)
Ltac crush2_step := match goal with
 | H : MOk _ = MOk _ |- _ => injection H as H; subst
 | H : LOk _ = LOk _ |- _ => injection H as H; subst
 | H : Some _ = Some _ |- _ => injection H as H; subst
 | H : inl _ = inl _ |- _ => injection H as H; subst
 | H : VSym _ = VSym _ |- _ => injection H as H; subst
 | H : ?a = ?a |- _ => clear H
 | H : _ = _ |- _ => discriminate H
 | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
 | H : sv_eqb _ _ = true |- _ => apply sv_eqb_eq in H; subst
 | H : is_true _ = true |- _ => apply sv_eqb_eq in H; subst
 | H : is_false _ = true |- _ => apply sv_eqb_eq in H; subst
 | H : exists _, _ |- _ => destruct H
 | H : _ /\ _ |- _ => destruct H
 | H : lookup ?x ?s = Some ?w |- context [lookup ?x ?s] => rewrite H
 | H : is_str ?v = true |- _ => is_var v; destruct v; try discriminate H; clear H
 | H : is_num ?v = true |- _ => is_var v; destruct v; try discriminate H; clear H
 | H : context [match ?x with _ => _ end] |- _ =>
     tryif is_var x then fail else (no_match_inside x; destruct x eqn:?)
 | H : context [match ?x with _ => _ end] |- _ =>
     is_var x; lazymatch type of x with sv => destruct x end
 end.
Ltac crush2 := repeat (crush2_step; simpl in * |-).
Ltac norm_up := repeat match goal with H : context [upcase_ascii ?c] |- _ =>
 let r := eval vm_compute in (upcase_ascii c) in change (upcase_ascii c) with r in H end.
Ltac prep Hg He := unfold callf in Hg, He; cbn [c_guard c_rhs c_pats fill] in *; simpl in Hg, He;
 unfold apply_builtin, cl_sym, shen_bool in Hg, He; simpl in Hg, He; norm_up; simpl in Hg, He.

Definition seq_ok (v r : sv) := (exists a b, v = VCons a b) /\ (exists c d, r = VCons c d) /\ SeqEquiv v r.


Ltac use_ih IH := eapply IH; [eassumption | assumption].
Ltac fn_side := first [reflexivity | (unfold TRUEP; discriminate)].
Ltac opt_finish IHo IHs :=
 first
 [ apply sem_true
 | apply sem_if_tf
 | apply sem_quote_true
 | apply sem_quote_false
 | apply (sem_let false); use_ih IHo
 | apply (sem_let true); use_ih IHo
 | apply sem_ifb; use_ih IHo
 | apply sem_and; use_ih IHo
 | apply sem_or; use_ih IHo
 | apply sem_not; [apply (pc_not C) | apply (pc_cl_not C) | use_ih IHo]
 | apply sem_progn; match goal with H : run _ _ _ _ [?f] = LOk ?r |- _ =>
     let Hs := fresh in destruct (IHs f r H ltac:(assumption)) as [_ [_ Hs]]; exact Hs end
 | apply sem_null_right
 | apply sem_null_left
 | apply sem_fail_left
 | apply sem_fail_right
 | apply sem_pred1; [fn_side|fn_side|fn_side|fn_side|first [apply (pc_cons C)|apply (pc_string C)
     |apply (pc_number C)|apply (pc_empty C)]]
 | apply sem_pred2; [fn_side|fn_side|fn_side|fn_side|first [apply (pc_greater C)|apply (pc_greater_eq C)
     |apply (pc_less C)|apply (pc_less_eq C)|apply (pc_absequal C)]]
 | eapply sem_same2_lit_left; [fn_side|fn_side|fn_side|fn_side|apply pure_str|intros; apply (proj1 (pc_string_equal C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_str|intros; apply (proj2 (pc_string_equal C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_num|intros; apply (proj1 (pc_numeric C _ _))]
 | eapply sem_swap_lit; [fn_side|fn_side|fn_side|fn_side|apply pure_num|intros; apply (proj2 (pc_numeric C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_quote|
     intros; apply (proj1 (pc_symbol_eq C _ _ ltac:(eapply qlocal_right; eassumption)))]
 | eapply sem_swap_lit; [fn_side|fn_side|fn_side|fn_side|apply pure_quote|
     intros; apply (proj2 (pc_symbol_eq C _ _ ltac:(eapply qlocal_left; eassumption)))]
 ].

Theorem optimise_sound : forall ce n,
 (forall v r, run n expected_defs ce OPT [v] = LOk r -> qsafe v = true -> OptEquiv v r) /\
 (forall v r, run n expected_defs ce SEQ [v] = LOk r -> qsafe v = true -> seq_ok v r).
Proof.
 intros ce n. induction n as [|n [IHo IHs]].
 - split; intros; discriminate.
 - split.
   + intros v r H Hq. rewrite run_S, assoc_opt in H.
     apply apply_clauses_sound in H as [c [s [Hin [Hm [Hg He]]]]].
     unfold opt_clauses in Hin. simpl in Hin.
     repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end.
     all: apply match_pats1 in Hm; pose proof (match_pat_fill _ _ _ _ Hm eq_refl) as Hv; subst v; clear Hm.
     all: revert Hq; prep Hg He; crush2; intros Hq; qsplit.
     all: opt_finish IHo IHs.
   + intros v r H Hq. rewrite run_S, assoc_seq in H.
     apply apply_clauses_sound in H as [c [s [Hin [Hm [Hg He]]]]].
     unfold seq_clauses in Hin. simpl in Hin.
     repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end.
     all: apply match_pats1 in Hm; pose proof (match_pat_fill _ _ _ _ Hm eq_refl) as Hv; subst v; clear Hm.
     all: revert Hq; prep Hg He; crush2; intros Hq; qsplit.
     * split; [eauto | split; [eauto | apply sem_seq_one; use_ih IHo]].
     * match goal with H : run _ _ _ _ [?f] = LOk ?r |- _ =>
         destruct (IHs f r H ltac:(assumption)) as [[a [b ->]] [[c [d ->]] Hs]] end.
       split; [eauto | split; [eauto | apply sem_seq_cons; exact Hs]].
Qed.

(* ----- emit-boolean and emit-if ----- *)
Theorem emit_boolean_shape : forall ce n p r, run n expected_defs ce EMIT_BOOL [p] = LOk r ->
 r = f4 "IF" p (f2 "QUOTE" (VSym "true")) (f2 "QUOTE" (VSym "false")).
Proof.
 intros ce n p r H. destruct n as [|n]; [discriminate|]. rewrite run_S, assoc_emit_boolean in H.
 apply apply_clauses_sound in H as [c [s [Hin [Hm [Hg He]]]]].
 unfold emit_boolean_clauses in Hin. simpl in Hin.
 repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end.
 apply match_pats1 in Hm. pose proof (match_pat_fill _ _ _ _ Hm eq_refl) as Hv. subst p. clear Hm.
 prep Hg He. crush2. reflexivity.
Qed.

(* What emit-boolean builds is test-equivalent to its CL predicate; this is
   why optimise-boolean-check may strip it again (its first clause). *)
Theorem emit_boolean_test : forall p, OptEquiv (f4 "IF" p (f2 "QUOTE" (VSym "true")) (f2 "QUOTE" (VSym "false"))) p.
Proof. apply sem_if_tf. Qed.

Definition shen_if e c a b s o :=
 (exists s1, SHT e c s (TT s1) /\ ev e a s1 o) \/ (exists s1, SHT e c s (TF s1) /\ ev e b s1 o) \/
 (exists x s1, SHT e c s (TR x s1) /\ o = Raise x s1) \/ (exists v s1, SHT e c s (TB v s1) /\ o = BoolErr v s1).

Lemma generated_if : forall c c' a b, OptEquiv c c' -> forall e s o, ev e (f4 "IF" c' a b) s o <-> shen_if e c a b s o.
Proof.
 intros c c' a b H e s o. rewrite obs_cl_if. unfold shen_if.
 split; intros [[s1 [Hc Ha]]|[[s1 [Hc Hb]]|[[x [s1 [Hc ->]]]|[v [s1 [Hc ->]]]]]];
 solve [left; exists s1; split; [apply H|]; auto
       | right; left; exists s1; split; [apply H|]; auto
       | right; right; left; exists x, s1; split; [apply H|]; auto
       | right; right; right; exists v, s1; split; [apply H|]; auto].
Qed.

Theorem emit_if_refines : forall ce n t th el sc r,
 run n expected_defs ce EMIT_IF [t; th; el; sc] = LOk r ->
 (t = VSym "true" /\ ce th sc = LOk r) \/
 (t = VSym "false" /\ ce el sc = LOk r) \/
 (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\
   (qsafe c = true -> forall e s o, ev e r s o <-> shen_if e c a b s o)).
Proof.
 intros ce n t th el sc r H. destruct n as [|n]; [discriminate|]. rewrite run_S, assoc_emit_if in H.
 apply apply_clauses_sound in H as [c [s [Hin [Hm [Hg He]]]]].
 unfold emit_if_clauses in Hin. simpl in Hin.
 repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end;
 simpl in Hm; prep Hg He; crush2.
 - left. split; auto.
 - right; left. split; auto.
 - right; right. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
   intros Hq e s o. apply generated_if.
   destruct (optimise_sound ce n) as [Ho _]. eapply Ho; eassumption.
Qed.

End CL.
Arguments Ok {St}. Arguments Raise {St}. Arguments BoolErr {St}.
Arguments TT {St}. Arguments TF {St}. Arguments TR {St}. Arguments TB {St}.

(* ---------- 6. The true? rule is the captured shen-cl.true? ---------- *)
Definition guard_abs (v : sv) : CLPortGuard.CLPortGuard.value :=
 if is_true v then CLPortGuard.CLPortGuard.ShenTrue
 else if is_false v then CLPortGuard.CLPortGuard.ShenFalse
 else match v with
      | VNil => CLPortGuard.CLPortGuard.HostNil
      | VSym x => if String.eqb x "T" then CLPortGuard.CLPortGuard.HostTrue else CLPortGuard.CLPortGuard.Other 0
      | _ => CLPortGuard.CLPortGuard.Other 0 end.
Definition guard_out {St} (v : sv) (s : St) (r : CLPortGuard.CLPortGuard.result) : out St :=
 match r with
 | CLPortGuard.CLPortGuard.Returned CLPortGuard.CLPortGuard.HostTrue => Ok (VSym "T") s
 | CLPortGuard.CLPortGuard.Returned CLPortGuard.CLPortGuard.HostNil => Ok VNil s
 | _ => BoolErr v s end.
(* The evaluator's shen-cl.true? rule coincides with running the captured
   Shen-CL primitives.lsp DEFUN in CLPortGuard's model. *)
Theorem guard_rule_is_captured_guard : forall St v (s : St),
 guard_result St v s = guard_out v s (CLPortGuard.CLPortGuard.run CLPortCapture.captured_guard (guard_abs v)).
Proof.
 intros St v s. rewrite CLPortCapture.captured_guard_correct. unfold guard_result, guard_abs, guard_out.
 destruct (is_true v); [reflexivity|]. destruct (is_false v); [reflexivity|].
 destruct v; try reflexivity. destruct (String.eqb s0 "T"); reflexivity.
Qed.

(* ---------- 7. The contracts are jointly satisfiable ---------- *)
(* A concrete deterministic world. It shows the hypotheses are consistent,
   so the universal theorems are not vacuous; it is not a model of SBCL. *)
Definition mbool (b : bool) : sv := if b then VSym "true" else VSym "false".
Definition hbool (b : bool) : sv := if b then VSym "T" else VNil.
Definition is_cons v := match v with VCons _ _ => true | _ => false end.
Definition is_nil v := match v with VNil => true | _ => false end.
Definition meq a b := if symbolic a || symbolic b then sv_eqb a b
 else match a, b with VObj n, VObj m => Nat.eqb n m | _, _ => false end.
Definition mcmp (f : string) (x y : string) : bool :=
 if String.eqb f "gt" then String.ltb y x else if String.eqb f "ge" then negb (String.ltb x y)
 else if String.eqb f "lt" then String.ltb x y else negb (String.ltb y x).
Definition cmp_kind (f : string) : option (string * bool) :=
 if String.eqb f "shen-cl.greater?" then Some ("gt", true) else if String.eqb f ">" then Some ("gt", false)
 else if String.eqb f "shen-cl.greater-than-or-equal-to?" then Some ("ge", true) else if String.eqb f ">=" then Some ("ge", false)
 else if String.eqb f "shen-cl.less?" then Some ("lt", true) else if String.eqb f "<" then Some ("lt", false)
 else if String.eqb f "shen-cl.less-than-or-equal-to?" then Some ("le", true) else if String.eqb f "<=" then Some ("le", false)
 else None.
Definition pred1 (f : string) : option ((sv -> bool) * bool) :=
 if String.eqb f "cons?" then Some (is_cons, true) else if String.eqb f "CONSP" then Some (is_cons, false)
 else if String.eqb f "string?" then Some (is_str, true) else if String.eqb f "STRINGP" then Some (is_str, false)
 else if String.eqb f "number?" then Some (is_num, true) else if String.eqb f "NUMBERP" then Some (is_num, false)
 else if String.eqb f "empty?" then Some (is_nil, true) else if String.eqb f "NULL" then Some (is_nil, false)
 else None.
Definition res (shen : bool) (b : bool) : out unit := Ok (if shen then mbool b else hbool b) tt.
Definition model_fn (f : string) (vs : list sv) : option (out unit) :=
 match vs with
 | [] => if String.eqb f "fail" then Some (Ok (VSym "shen.fail!") tt) else None
 | [v] => match pred1 f with
   | Some (p, sh) => Some (res sh (p v))
   | None => if String.eqb f "not" then Some (shen_not_result unit v tt)
             else if String.eqb f "NOT" then Some (cl_not_result unit v tt) else None end
 | [a; b] =>
   if String.eqb f EQUALP then Some (res true (sv_eqb a b))
   else if String.eqb f "shen-cl.absequal" then Some (res false (sv_eqb a b))
   else if String.eqb f "EQUAL" then Some (res false (sv_eqb a b))
   else if String.eqb f "EQ" then Some (res false (meq a b))
   else if String.eqb f "shen-cl.numeric-equal" then Some (res false (is_num a && sv_eqb a b))
   else match cmp_kind f with
     | Some (k, sh) => match a, b with
       | VNum x, VNum y => Some (res sh (mcmp k x y))
       | _, _ => Some (Raise (VObj 0) tt) end
     | None => None end
 | _ => None end.
Definition model_prim (f : string) (vs : list sv) (s : unit) (o : out unit) : Prop := model_fn f vs = Some o.

Lemma refine_by_fn : forall f xs g ys,
 match model_fn f xs, model_fn g ys with
 | Some o1, Some o2 => shen_test unit o1 = cl_test unit o2
 | None, None => True | _, _ => False end ->
 args_refine unit model_prim f xs g ys.
Proof.
 intros f xs g ys H s t. unfold model_prim.
 destruct (model_fn f xs) as [o1|], (model_fn g ys) as [o2|]; try contradiction.
 - split; intros [o [Ho Ht]]; injection Ho as <-; [exists o2 | exists o1]; split; congruence.
 - split; intros [o [Ho Ht]]; discriminate.
Qed.
Lemma res_test : forall b, shen_test unit (res true b) = cl_test unit (res false b).
Proof. destruct b; reflexivity. Qed.
Lemma sv_eqb_sym : forall a b, sv_eqb a b = sv_eqb b a.
Proof.
 intros a b. destruct (sv_eqb a b) eqn:E; symmetry.
 - apply sv_eqb_eq in E. subst. apply sv_eqb_eq. reflexivity.
 - destruct (sv_eqb b a) eqn:F; auto. apply sv_eqb_eq in F. subst.
   rewrite (proj2 (sv_eqb_eq a a) eq_refl) in E. discriminate.
Qed.

Lemma pred_model : forall f g p, pred1 f = Some (p, true) -> pred1 g = Some (p, false) ->
 cmp_kind f = None -> cmp_kind g = None -> String.eqb f EQUALP = false -> String.eqb g EQUALP = false ->
 pred_refines unit model_prim f g.
Proof.
 intros f g p Hf Hg Cf Cg Ef Eg vs. apply refine_by_fn. unfold model_fn.
 destruct vs as [|v [|w [|x r]]].
 - destruct (String.eqb f "fail") eqn:F1; [apply String.eqb_eq in F1; subst; discriminate|].
   destruct (String.eqb g "fail") eqn:G1; [apply String.eqb_eq in G1; subst; discriminate|]. exact I.
 - rewrite Hf, Hg. apply res_test.
 - rewrite Ef, Eg. destruct (String.eqb f "shen-cl.absequal") eqn:F1; [apply String.eqb_eq in F1; subst; discriminate|].
   destruct (String.eqb g "shen-cl.absequal") eqn:G1; [apply String.eqb_eq in G1; subst; discriminate|].
   destruct (String.eqb f "EQUAL") eqn:F2; [apply String.eqb_eq in F2; subst; discriminate|].
   destruct (String.eqb g "EQUAL") eqn:G2; [apply String.eqb_eq in G2; subst; discriminate|].
   destruct (String.eqb f "EQ") eqn:F3; [apply String.eqb_eq in F3; subst; discriminate|].
   destruct (String.eqb g "EQ") eqn:G3; [apply String.eqb_eq in G3; subst; discriminate|].
   destruct (String.eqb f "shen-cl.numeric-equal") eqn:F4; [apply String.eqb_eq in F4; subst; discriminate|].
   destruct (String.eqb g "shen-cl.numeric-equal") eqn:G4; [apply String.eqb_eq in G4; subst; discriminate|].
   rewrite Cf, Cg. exact I.
 - exact I.
Qed.

Lemma cmp_model : forall f g k, cmp_kind f = Some (k, true) -> cmp_kind g = Some (k, false) ->
 pred1 f = None -> pred1 g = None ->
 String.eqb f EQUALP = false -> String.eqb g EQUALP = false ->
 String.eqb f "shen-cl.absequal" = false -> String.eqb g "shen-cl.absequal" = false ->
 String.eqb f "EQUAL" = false -> String.eqb g "EQUAL" = false -> String.eqb f "EQ" = false -> String.eqb g "EQ" = false ->
 String.eqb f "shen-cl.numeric-equal" = false -> String.eqb g "shen-cl.numeric-equal" = false ->
 String.eqb f "fail" = false -> String.eqb g "fail" = false ->
 String.eqb f "not" = false -> String.eqb g "not" = false -> String.eqb f "NOT" = false -> String.eqb g "NOT" = false ->
 pred_refines unit model_prim f g.
Proof.
 intros f g k Hf Hg Pf Pg E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 vs. apply refine_by_fn. unfold model_fn.
 destruct vs as [|v [|w [|x r]]].
 - rewrite E11, E12. exact I.
 - rewrite Pf, Pg, E13, E14, E15, E16. exact I.
 - rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, Hf, Hg.
   destruct v; destruct w; try reflexivity. apply res_test.
 - exact I.
Qed.

Theorem model_contracts : primitive_contracts unit model_prim.
Proof.
 constructor.
 1-4: intros v; eapply pred_model; reflexivity.
 1-4: intros v w; eapply cmp_model; reflexivity.
 - intros v w. apply refine_by_fn. apply res_test.
 - intros v [] o. unfold model_prim. simpl. split; [congruence | intros ->; reflexivity].
 - intros v [] o. unfold model_prim. simpl. split; [congruence | intros ->; reflexivity].
 - intros v. apply refine_by_fn. simpl. destruct v; reflexivity.
 - intros v. apply refine_by_fn. simpl. destruct v; reflexivity.
 - intros s a s1 H v. unfold model_prim in H. simpl in H. injection H as <- <-. split; apply refine_by_fn; simpl;
   unfold meq; simpl; [apply res_test | rewrite orb_true_r; apply res_test].
 - intros x v. split; apply refine_by_fn; simpl; apply res_test.
 - intros n v. split; apply refine_by_fn; simpl; [|rewrite sv_eqb_sym]; destruct v; simpl; first [reflexivity | apply res_test].
 - intros d v Hd. destruct d; try discriminate Hd; split; apply refine_by_fn; simpl; destruct v; simpl;
   first [reflexivity | apply res_test | (rewrite String.eqb_sym; apply res_test)].
Qed.

(* ---------- 8. Statements about any admitted capture ---------- *)
Theorem admitted_optimise_sound : forall L St prim other ce n v r,
 admitted_lowering L = true -> primitive_contracts St prim ->
 run n (lowering_defs L) ce OPT [v] = LOk r -> qsafe v = true -> OptEquiv St prim other v r.
Proof.
 intros L St prim other ce n v r HL C H Hq. rewrite admitted_defs in H by exact HL.
 exact (proj1 (optimise_sound St prim other C ce n) v r H Hq).
Qed.
Theorem admitted_emit_if_refines : forall L St prim other ce n t th el sc r,
 admitted_lowering L = true -> primitive_contracts St prim ->
 run n (lowering_defs L) ce EMIT_IF [t; th; el; sc] = LOk r ->
 (t = VSym "true" /\ ce th sc = LOk r) \/
 (t = VSym "false" /\ ce el sc = LOk r) \/
 (exists c a b, ce t sc = LOk c /\ ce th sc = LOk a /\ ce el sc = LOk b /\
   (qsafe c = true -> forall e s o, ev St prim other e r s o <-> shen_if St prim other e c a b s o)).
Proof.
 intros L St prim other ce n t th el sc r HL C H. rewrite admitted_defs in H by exact HL.
 exact (emit_if_refines St prim other C ce n t th el sc r H).
Qed.
