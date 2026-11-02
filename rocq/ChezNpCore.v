(* E2E-22: a core semantics for the expression languages L4 and L4.5 of Chez
   Scheme 10.3.0's nanopass compiler, restricted to the constructs this lane
   validates, and a translation validator for np-recognize-mrvs (L4 -> L4.5).

   Scope and assumptions, stated here so no claim outgrows them:
   * Terms are Chez's own *unparsed* pass output (the tracer's ir-printer):
     the unparse forms of np-languages.ss (L4 (call info e0 e1 ...) prints as
     (e0 e1 ...); L4.5 (call info mdcl e0 e1 ...) prints as
     (call mdcl e0 e1 ...)), seq chains flattened to begin by flatten-seq.
     The unparser omits every info field of these forms (application flags,
     lambda names, clause info).  The semantics below therefore does not read
     info; a pass that changed only info would be invisible here.  This is an
     explicit limitation, not a claim that info is irrelevant to Chez.
   * Supported constructs: uvar references, primrefs, quote, application,
     if, begin, let, letrec, and case-lambda clauses of fixed arity
     (interface = number of formals).  Everything else (foreign, fcallable,
     profile, pariah, rest clauses, mvcall, mvlet, direct-call labels) makes
     the denotation None, so the validator rejects.
   * Argument evaluation order in Chez is unspecified.  [eval] takes an
     arbitrary order policy; every theorem below holds for every policy.
   * Primitive behaviour is an arbitrary parameter [prim] over an arbitrary
     world type; theorems hold for every primitive semantics. *)
From Coq Require Import String List Bool Arith ZArith.
From Buri Require Import ChezNpReader.
Import ListNotations.
Open Scope string_scope.

Inductive cexpr : Type :=
| CVar : string -> cexpr
| CPrim : sexp -> cexpr
| CQuote : sexp -> cexpr
| CCall : cexpr -> list cexpr -> cexpr
| CIf : cexpr -> cexpr -> cexpr -> cexpr
| CSeq : cexpr -> cexpr -> cexpr
| CLam : list (list string * cexpr) -> cexpr
| CLet : list (string * cexpr) -> cexpr -> cexpr
| CLetrec : list (string * list (list string * cexpr)) -> cexpr -> cexpr.

Definition cexpr_eq_dec : forall x y : cexpr, {x = y} + {x <> y}.
Proof.
  fix IH 1; intros x y; decide equality;
    try apply string_dec; try apply sexp_eq_dec;
    try (apply list_eq_dec; exact IH);
    try (apply list_eq_dec; intros [a1 b1] [a2 b2];
         first [ destruct (string_dec a1 a2) | destruct (list_eq_dec string_dec a1 a2) ];
         [ subst | right; congruence ];
         first [ destruct (IH b1 b2)
               | destruct (list_eq_dec (fun p q : list string * cexpr =>
                    ltac:(decide equality; first [exact (IH _ _) | apply list_eq_dec, string_dec])) b1 b2) ];
         [ left; congruence | right; congruence ]).
Defined.

(* ---- lexical classes of the printed forms ------------------------------ *)

Fixpoint all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => is_digit c && all_digits r
  end.

(* With print-gensym 'pretty/suffix a uvar prints as NAME.N. *)
Fixpoint uvar_suffix (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c r =>
      (is c 46 && negb (String.eqb r "") && all_digits r) || uvar_suffix r
  end.

Definition is_uvar_atom (x : sexp) : option string :=
  match x with Atom a => if uvar_suffix a then Some a else None | _ => None end.

Definition is_primref (x : sexp) : bool :=
  match x with
  | Rec (Atom a :: _) => prefix "primref." a
  | _ => false
  end.

Definition nat_of_atom (x : sexp) : option nat :=
  match x with
  | Atom a => if andb (negb (String.eqb a "")) (all_digits a) then Some (digits_nat a) else None
  | _ => None
  end.

Fixpoint uvars (xs : list sexp) : option (list string) :=
  match xs with
  | [] => Some []
  | x :: r =>
      match is_uvar_atom x, uvars r with
      | Some a, Some l => Some (a :: l)
      | _, _ => None
      end
  end.

Definition l4_keyword (a : string) : bool :=
  existsb (String.eqb a)
    ["case-lambda"; "quote"; "if"; "begin"; "letrec"; "let"; "foreign";
     "fcallable"; "profile"; "pariah"; "set!"; "moi"; "seq"; "call"; "mvcall"; "mvlet";
     "label"; "loop"; "foreign-call"; "attachment-set"; "attachment-get";
     "attachment-consume"; "continuation-get"; "continuation-set"].

(* ---- denotation of printed L4 / L4.5 expressions ----------------------- *)

(* [mrv] selects the language: false = L4, true = L4.5. *)
Fixpoint denote (mrv : bool) (fuel : nat) (x : sexp) : option cexpr :=
  match fuel with
  | O => None
  | S f =>
      let fix dlist (xs : list sexp) : option (list cexpr) :=
        match xs with
        | [] => Some []
        | y :: ys =>
            match denote mrv f y, dlist ys with
            | Some c, Some cs => Some (c :: cs)
            | _, _ => None
            end
        end in
      let dclause (c : sexp) : option (list string * cexpr) :=
        match c with
        | Lst [Atom kw; Lst xs; n; body] =>
            if String.eqb kw "clause" then
              match uvars xs, nat_of_atom n, denote mrv f body with
              | Some ps, Some k, Some b => if Nat.eqb k (length ps) then Some (ps, b) else None
              | _, _, _ => None
              end
            else None
        | _ => None
        end in
      let fix dclauses (cs : list sexp) : option (list (list string * cexpr)) :=
        match cs with
        | [] => Some []
        | c :: r =>
            match dclause c, dclauses r with
            | Some a, Some b => Some (a :: b)
            | _, _ => None
            end
        end in
      let dlam (x : sexp) : option (list (list string * cexpr)) :=
        match x with
        | Lst (Atom kw :: cs) => if String.eqb kw "case-lambda" then dclauses cs else None
        | _ => None
        end in
      let fix dbinds (bs : list sexp) : option (list (string * cexpr)) :=
        match bs with
        | [] => Some []
        | Lst [v; e] :: r =>
            match is_uvar_atom v, denote mrv f e, dbinds r with
            | Some a, Some c, Some cs => Some ((a, c) :: cs)
            | _, _, _ => None
            end
        | _ => None
        end in
      let fix drecbinds (bs : list sexp) : option (list (string * list (list string * cexpr))) :=
        match bs with
        | [] => Some []
        | Lst [v; e] :: r =>
            match is_uvar_atom v, dlam e, drecbinds r with
            | Some a, Some c, Some cs => Some ((a, c) :: cs)
            | _, _, _ => None
            end
        | _ => None
        end in
      let fix dbegin (xs : list sexp) : option cexpr :=
        match xs with
        | [] => None
        | [y] => denote mrv f y
        | y :: ys =>
            match denote mrv f y, dbegin ys with
            | Some a, Some b => Some (CSeq a b)
            | _, _ => None
            end
        end in
      let app (g : sexp) (args : list sexp) : option cexpr :=
        match denote mrv f g, dlist args with
        | Some g', Some a' => Some (CCall g' a')
        | _, _ => None
        end in
      match x with
      | Atom _ => option_map CVar (is_uvar_atom x)
      | Rec _ => if is_primref x then Some (CPrim x) else None
      | Lst (Atom kw :: rest) =>
          if String.eqb kw "quote" then
            match rest with [d] => Some (CQuote d) | _ => None end
          else if String.eqb kw "case-lambda" then option_map CLam (dclauses rest)
          else if String.eqb kw "if" then
            match rest with
            | [a; b; c] =>
                match denote mrv f a, denote mrv f b, denote mrv f c with
                | Some a', Some b', Some c' => Some (CIf a' b' c')
                | _, _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "begin" then
            match rest with _ :: _ :: _ => dbegin rest | _ => None end
          else if String.eqb kw "let" then
            match rest with
            | [Lst bs; body] =>
                match dbinds bs, denote mrv f body with
                | Some b, Some c => Some (CLet b c)
                | _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "letrec" then
            match rest with
            | [Lst bs; body] =>
                match drecbinds bs, denote mrv f body with
                | Some b, Some c => Some (CLetrec b c)
                | _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "call" then
            (* L4.5 (call info #f e0 e1 ...) prints as (call #f e0 e1 ...):
               an ordinary application; a direct-call label is unsupported. *)
            if mrv then
              match rest with
              | Atom m :: g :: args => if String.eqb m "#f" then app g args else None
              | _ => None
              end
            else None
          else if l4_keyword kw then None
          (* an L4 application headed by an atom: the atom must be a uvar *)
          else if mrv then None else app (Atom kw) rest
      | Lst (g :: args) => if mrv then None else app g args
      | _ => None
      end
  end.

Definition denote_fuel : nat := 256.

(* Printed CaseLambdaExpr (the entry of L4 and L4.5) after removing
   print-graph labels. *)
Definition denote_program (mrv : bool) (x : sexp) : option cexpr :=
  match expand_graph x with
  | Some y =>
      match y with
      | Lst (Atom kw :: _) => if String.eqb kw "case-lambda" then denote mrv denote_fuel y else None
      | _ => None
      end
  | None => None
  end.

(* ---- core big-step semantics (fuel) ------------------------------------ *)

Inductive value : Type :=
| VDatum : sexp -> value
| VPrim : sexp -> value
| VClo : list (list string * cexpr) -> list frame -> value
with frame : Type :=
| FVal : string -> value -> frame
| FRec : list (string * list (list string * cexpr)) -> frame.

Section Eval.
  Variable World : Type.
  (* Arbitrary primitive semantics; None is a primitive failure. *)
  Variable prim : sexp -> list value -> World -> option (value * World).
  (* Arbitrary evaluation-order policy: given the number of subexpressions
     of an application (operator first), the order in which to evaluate
     them.  A policy that is not a permutation makes evaluation fail. *)
  Variable order : nat -> list nat.
  Variable truthy : value -> bool.

  Fixpoint lookup (x : string) (env : list frame) : option value :=
    match env with
    | [] => None
    | FVal y v :: r => if String.eqb x y then Some v else lookup x r
    | FRec bs :: r =>
        match find (fun b => String.eqb x (fst b)) bs with
        | Some (_, cls) => Some (VClo cls env)
        | None => lookup x r
        end
    end.

  Fixpoint bind (xs : list string) (vs : list value) (env : list frame) : option (list frame) :=
    match xs, vs with
    | [], [] => Some env
    | x :: xr, v :: vr => bind xr vr (FVal x v :: env)
    | _, _ => None
    end.

  Fixpoint select (cls : list (list string * cexpr)) (n : nat) : option (list string * cexpr) :=
    match cls with
    | [] => None
    | (ps, b) :: r => if Nat.eqb (length ps) n then Some (ps, b) else select r n
    end.

  Definition is_perm_of (k : nat) (o : list nat) : bool :=
    Nat.eqb (length o) k &&
    forallb (fun i => Nat.ltb i k) o &&
    (fix nodup (l : list nat) : bool :=
       match l with [] => true | i :: r => negb (existsb (Nat.eqb i) r) && nodup r end) o.

  Fixpoint place (i : nat) (v : value) (slots : list (option value)) : list (option value) :=
    match i, slots with
    | O, _ :: r => Some v :: r
    | S j, s :: r => s :: place j v r
    | _, [] => []
    end.

  Fixpoint all_some (xs : list (option value)) : option (list value) :=
    match xs with
    | [] => Some []
    | Some v :: r => option_map (cons v) (all_some r)
    | None :: _ => None
    end.

  Fixpoint eval_in_order (ev : cexpr -> World -> option (value * World))
      (o : list nat) (es : list cexpr) (slots : list (option value)) (w : World)
      : option (list (option value) * World) :=
    match o with
    | [] => Some (slots, w)
    | i :: r =>
        match nth_error es i with
        | Some ei =>
            match ev ei w with
            | Some (v, w') => eval_in_order ev r es (place i v slots) w'
            | None => None
            end
        | None => None
        end
    end.

  Fixpoint eval_binds (ev : cexpr -> World -> option (value * World))
      (bs : list (string * cexpr)) (w : World)
      : option (list (string * value) * World) :=
    match bs with
    | [] => Some ([], w)
    | (x, ex) :: r =>
        match ev ex w with
        | Some (v, w') =>
            match eval_binds ev r w' with
            | Some (vs, w'') => Some ((x, v) :: vs, w'')
            | None => None
            end
        | None => None
        end
    end.

  Definition apply_value (ev_body : list frame -> cexpr -> World -> option (value * World))
      (vs : list value) (w : World) : option (value * World) :=
    match vs with
    | VPrim p :: args => prim p args w
    | VClo cls cenv :: args =>
        match select cls (length args) with
        | Some (ps, b) =>
            match bind ps args cenv with
            | Some env' => ev_body env' b w
            | None => None
            end
        | None => None
        end
    | _ => None
    end.

  Definition call_with (ev : cexpr -> World -> option (value * World))
      (ap : list value -> World -> option (value * World))
      (g : cexpr) (args : list cexpr) (w : World) : option (value * World) :=
    let es := g :: args in
    let o := order (length es) in
    if is_perm_of (length es) o then
      match eval_in_order ev o es (map (fun _ => None) es) w with
      | Some (slots, w2) =>
          match all_some slots with
          | Some vs => ap vs w2
          | None => None
          end
      | None => None
      end
    else None.

  (* let right-hand sides are evaluated in printed order; the validators
     below never relate two different let orders. *)
  Fixpoint eval (fuel : nat) (env : list frame) (e : cexpr) (w : World)
    : option (value * World) :=
    match fuel with
    | O => None
    | S f =>
        match e with
        | CVar x => match lookup x env with Some v => Some (v, w) | None => None end
        | CPrim p => Some (VPrim p, w)
        | CQuote d => Some (VDatum d, w)
        | CLam cls => Some (VClo cls env, w)
        | CIf a b c =>
            match eval f env a w with
            | Some (v, w') => if truthy v then eval f env b w' else eval f env c w'
            | None => None
            end
        | CSeq a b =>
            match eval f env a w with
            | Some (_, w') => eval f env b w'
            | None => None
            end
        | CLet bs body =>
            match eval_binds (eval f env) bs w with
            | Some (vs, w') =>
                eval f (fold_left (fun acc p => FVal (fst p) (snd p) :: acc) vs env) body w'
            | None => None
            end
        | CLetrec bs body => eval f (FRec bs :: env) body w
        | CCall g args => call_with (eval f env) (apply_value (eval f)) g args w
        end
    end.
End Eval.

(* The semantics of a printed L4 (mrv = false) or L4.5 (mrv = true) program:
   evaluate its denotation, the entry case-lambda, applied to no arguments,
   as Chez's main wrapper is (compile.ss c-compile). *)
Definition sem (mrv : bool) {World} prim order truthy (fuel : nat) (x : sexp) (w : World)
  : option (option (value * World)) :=
  option_map (fun c => eval World prim order truthy fuel [] (CCall c []) w) (denote_program mrv x).

(* ---- np-recognize-mrvs validator --------------------------------------- *)

Definition same_some (oa ob : option cexpr) : bool :=
  match oa, ob with
  | Some a, Some b => if cexpr_eq_dec a b then true else false
  | _, _ => false
  end.

(* The validator.  It is a notation, not a definition, so that the kernel
   never has to convert between a checker constant and its body: that
   conversion forces it to unfold the fuelled denotation on open terms. *)
Notation check_recognize_mrvs input output :=
  (same_some (denote_program false input) (denote_program true output)) (only parsing).

(* Kept abstract over the two denotations so that checking the proof never
   unfolds the (fuelled) denotation functions. *)
Lemma same_denotation : forall oa ob : option cexpr,
  same_some oa ob = true -> exists c, oa = Some c /\ ob = Some c.
Proof.
  intros [a|] [b|] H; unfold same_some in H.
  - destruct (cexpr_eq_dec a b) as [E|E].
    + subst b. exists a. split; reflexivity.
    + exfalso. exact (Bool.diff_false_true H).
  - exfalso. exact (Bool.diff_false_true H).
  - exfalso. exact (Bool.diff_false_true H).
  - exfalso. exact (Bool.diff_false_true H).
Qed.

Theorem check_recognize_mrvs_sound :
  forall input output,
    check_recognize_mrvs input output = true ->
    (exists c, denote_program false input = Some c /\ denote_program true output = Some c) /\
    forall (World : Type) (prim : sexp -> list value -> World -> option (value * World))
      (order : nat -> list nat) (truthy : value -> bool) (fuel : nat) (w : World),
      sem false prim order truthy fuel input w = sem true prim order truthy fuel output w /\
      sem false prim order truthy fuel input w <> None.
Proof.
  intros input output H.
  destruct (same_denotation _ _ H) as [c [Ha Hb]].
  split.
  - exists c; split; assumption.
  - intros World prim order truthy fuel w.
    unfold sem. rewrite Ha, Hb.
    split; [reflexivity | discriminate].
Qed.

(* Same-language textual identity: when a pass's printed output equals its
   printed input in the same language, every semantics of the printed form
   agrees.  This says nothing about fields the unparser does not print. *)
Definition check_printed_identity (input output : sexp) : bool := sexp_eqb input output.

Theorem check_printed_identity_sound :
  forall input output, check_printed_identity input output = true ->
  forall (A : Type) (meaning : sexp -> A), meaning input = meaning output.
Proof.
  intros input output H A meaning.
  apply sexp_eqb_true in H. subst. reflexivity.
Qed.
