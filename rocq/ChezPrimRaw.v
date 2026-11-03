(* E2E-22 (chezprim lane): the raw, info-carrying nanopass dump and what it
   lets the Wave-C validators see.

   The capture ports/chez-np/tarm64le-buri-arm-add.raw.np was produced by a
   minimally patched Chez Scheme 10.3.0 (ports/chez-np/patches/
   np-trace-raw.patch): after each pass's usual unparsed output its tracer
   also prints the nanopass *raw* unparse of the same record, which keeps
   every production field, info fields included.  The dump script
   (ports/chez-np/scripts/np-dump-raw.ss) prints every field of every info
   record.  Patched tracer and dump script together are a trusted dumping
   tool (obligation OB-CHEZ-NP-RAW-DUMP); nothing here proves anything about
   them.

   Evidence kinds:
   * universal theorems: [denote_raw]-based checker soundness
     ([check_raw_sound]) and [opaque_atoms] bookkeeping;
   * ground derivations: every statement about [raw_sections].
   The semantic core ([ChezNpCore.eval]) is Wave C's, unchanged. *)
From Coq Require Import String List Bool Arith ZArith.
From Buri Require Import ChezNpReader ChezNpCore ChezNpCaptureInput ChezNpValidate ChezPrimRawInput.
Import ListNotations.
Open Scope string_scope.

(* ---- access to the packaged raw capture ------------------------------- *)

Definition sec_name (s : string * string * option string) : string :=
  let '(n, _, _) := s in n.
Definition sec_pretty (s : string * string * option string) : string :=
  let '(_, p, _) := s in p.
Definition sec_raw (s : string * string * option string) : option string :=
  let '(_, _, r) := s in r.

Definition find_raw_sec (name : string) : option (string * string * option string) :=
  find (fun s => String.eqb (sec_name s) name) raw_sections.

Definition raw_text (name : string) : option string :=
  match find_raw_sec name with Some s => sec_raw s | None => None end.
Definition raw_pretty_text (name : string) : option string :=
  option_map sec_pretty (find_raw_sec name).

Definition raw_datum (name : string) : option sexp :=
  match raw_text name with Some t => read_exactly t | None => None end.
Definition raw_pretty_datum (name : string) : option sexp :=
  match raw_pretty_text name with Some t => read_exactly t | None => None end.

(* Ground derivation: the raw capture traced the same 66 pass outputs, in
   the same order, as the Wave-C stock capture. *)
Theorem raw_trace_pass_order : map sec_name raw_sections = map fst np_sections.
Proof. vm_compute. reflexivity. Qed.

(* Ground derivation: exactly the register allocator's 26 sub-pass outputs
   and np-generate-code print no raw form (their tracers do not go through
   the patched ir-printer); every other pass, 39 of them, does. *)
Definition no_raw_names : list string :=
  map sec_name (filter (fun s => match sec_raw s with Some _ => false | None => true end) raw_sections).

Theorem raw_coverage :
  length (filter (fun s => match sec_raw s with Some _ => true | None => false end) raw_sections) = 39 /\
  no_raw_names =
  ["do-live-analysis!"; "record-call-live!"; "do-spillable-conflict!"; "assign-frame!";
   "record-inspector-information!"; "assign-new-frame!"; "record-fp-offsets!";
   "finalize-frame-locations!"; "select-instructions!"; "do-unspillable-conflict!";
   "assign-registers!"; "finalize-register-locations!"; "expose-overflow-check-blocks!";
   "do-live-analysis!"; "record-call-live!"; "do-spillable-conflict!"; "assign-frame!";
   "record-inspector-information!"; "assign-new-frame!"; "record-fp-offsets!";
   "finalize-frame-locations!"; "select-instructions!"; "do-unspillable-conflict!";
   "assign-registers!"; "finalize-register-locations!"; "expose-overflow-check-blocks!";
   "np-generate-code"].
Proof. vm_compute. split; reflexivity. Qed.

(* Ground derivation: the patched build's np-generate-code output is the
   stock build's, character for character, so the raw capture describes the
   compilation whose 152 bytes ChezNpValidate checks. *)
Theorem raw_codegen_same :
  raw_pretty_text "np-generate-code" = section_text "np-generate-code".
Proof. vm_compute. reflexivity. Qed.

(* Every raw section reads as exactly one datum. *)
Definition all_raw_read : bool :=
  forallb (fun s => match sec_raw s with
                    | Some t => match read_exactly t with Some _ => true | None => false end
                    | None => true end) raw_sections.

Theorem raw_sections_read : all_raw_read = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- what is still not printed ---------------------------------------- *)

(* Opaque printed objects (#<...>) in a datum: the only places where the raw
   dump still hides content. *)
Fixpoint opaque_atoms (x : sexp) : list string :=
  let fix go (xs : list sexp) : list string :=
    match xs with [] => [] | y :: ys => app (opaque_atoms y) (go ys) end in
  match x with
  | Atom a => if prefix "#<" a then [a] else []
  | Lst xs | Vec xs | Rec xs => go xs
  | Dot xs t => app (go xs) (opaque_atoms t)
  | Def _ y => opaque_atoms y
  | _ => []
  end.

Definition opaque_of (name : string) : list string :=
  match raw_datum name with Some d => nodup string_dec (opaque_atoms d) | None => ["#<unread>"] end.

(* The 31 traced expression-language passes, L1 (cpnanopass) to L14
   (np-expose-allocation-pointer). *)
Definition expression_passes : list string := firstn 31 (map fst np_sections).

Definition block_passes : list string :=
  ["np-expose-basic-blocks"; "np-remove-repeater-blocks!"; "np-propagate-pariahty!";
   "np-add-in-links!"; "np-compute-loop-depth!"; "np-weight-references!";
   "np-remove-repeater-blocks-again!"; "np-optimize-block-order!"].

(* Ground derivation.  In the raw output of every expression-language pass
   the only opaque object is the quoted constant #<void> (a datum, not hidden
   IR).  In the block languages L15a and L16 two kinds of content remain
   hidden: live-info records, and the assembler procedures that L16 [asm]
   forms (and the L15a/L16 instruction records) carry. *)
Theorem raw_opaque_census :
  last expression_passes "" = "np-expose-allocation-pointer" /\
  forallb (fun n => forallb (String.eqb "#<void>") (opaque_of n)) expression_passes = true /\
  nodup string_dec (flat_map opaque_of block_passes) =
  ["#<live-info>"; "#<procedure asm-check-flag-internal>"; "#<procedure asm-relop-internal>";
   "#<procedure>"; "#<procedure asm-kill>"; "#<procedure asm-asm-call-internal>"].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- printed identity, re-checked on the raw form ------------------------ *)

Definition raw_identity_holds (p : string * string * string) : bool :=
  let '(a, b, _) := p in
  match raw_datum a, raw_datum b with
  | Some x, Some y => check_printed_identity x y
  | _, _ => false
  end.

(* Ground derivation.  Nine of Wave C's ten printed-identity passes are
   identities of the raw form too, info fields included.  The tenth,
   np-suppress-procedure-checks, is not: it changes info-call fields, which
   the stock printer hid.  It is validated semantically below. *)
Theorem raw_identity_passes :
  map raw_identity_holds identity_passes =
  [true; false; true; true; true; true; true; true; true; true] /\
  nth 1 (map (fun p => let '(_, b, _) := p in b) identity_passes) "" = "np-suppress-procedure-checks".
Proof. vm_compute. split; reflexivity. Qed.

(* ---- a denotation of raw L4 / L4.5 that reads info fields ---------------- *)

(* Fields of a dumped record #[info:T f1= v1 f2= v2 ...]. *)
Fixpoint field_names (fs : list sexp) : option (list string) :=
  match fs with
  | [] => Some []
  | Atom k :: _ :: r => option_map (cons k) (field_names r)
  | _ => None
  end.

Fixpoint field (k : string) (fs : list sexp) : option sexp :=
  match fs with
  | Atom k' :: v :: r => if String.eqb k k' then Some v else field k r
  | _ => None
  end.

Definition list_string_eqb (a b : list string) : bool :=
  if list_eq_dec string_dec a b then true else false.

Definition is_bool_atom (o : option sexp) : bool :=
  match o with Some (Atom a) => String.eqb a "#t" || String.eqb a "#f" | _ => false end.

Definition is_atom (s : string) (o : option sexp) : bool :=
  match o with Some (Atom a) => String.eqb a s | _ => false end.

Definition info_call_fields : list string :=
  ["src="; "sexpr="; "check?="; "pariah?="; "error?="; "shift-attachment?=";
   "shift-consumer-attachment?*="].

(* An info-call record is accepted when it has exactly the Chez 10.3.0
   fields, no continuation-attachment shifting, and a check? flag that is #t,
   or #f only for a primref operator.  A primref denotes a procedure, so the
   procedure check that check?= #t requests cannot fail there and check?= #f
   omits nothing; for any other operator check?= #f would leave applying a
   non-procedure undefined, which this denotation does not model, so it
   rejects.  src, sexpr (source data), pariah? and error? (block-placement
   hints) do not affect the value. *)
Definition call_info_ok (info : sexp) (op_is_primref : bool) : bool :=
  match info with
  | Rec (Atom ty :: fs) =>
      String.eqb ty "info:info-call" &&
      match field_names fs with Some ns => list_string_eqb ns info_call_fields | None => false end &&
      is_atom "#f" (field "shift-attachment?=" fs) &&
      (match field "shift-consumer-attachment?*=" fs with Some (Lst []) => true | _ => false end) &&
      is_bool_atom (field "pariah?=" fs) && is_bool_atom (field "error?=" fs) &&
      (is_atom "#t" (field "check?=" fs) || (is_atom "#f" (field "check?=" fs) && op_is_primref))
  | _ => false
  end.

Definition info_lambda_fields : list string :=
  ["src="; "sexpr="; "libspec="; "interface*="; "dcl*="; "flags="; "fv*="; "name=";
   "well-known?="; "closure-rep="; "ctci="; "pinfo*="; "seqno="].

(* An info-lambda record must have the Chez 10.3.0 fields and an interface*
   list equal to the clauses' interface numbers. *)
Definition lambda_info_ok (info : sexp) (ifaces : list sexp) : bool :=
  match info with
  | Rec (Atom ty :: fs) =>
      String.eqb ty "info:info-lambda" &&
      match field_names fs with Some ns => list_string_eqb ns info_lambda_fields | None => false end &&
      match field "interface*=" fs with Some (Lst xs) => sexp_eqb (Lst xs) (Lst ifaces) | _ => false end
  | _ => false
  end.

Definition clause_iface (c : sexp) : sexp :=
  match c with Lst [_; _; n; _] => n | _ => Atom "" end.

(* Raw L4 (mrv = false) and L4.5 (mrv = true): (case-lambda INFO clause ...),
   (clause (x ...) n body), (call INFO e0 e1 ...) resp.
   (call INFO #f e0 e1 ...), (seq e1 e2), quote, if, let, letrec, uvar atoms
   and primref records; anything else is rejected. *)
Fixpoint denote_raw (mrv : bool) (fuel : nat) (x : sexp) : option cexpr :=
  match fuel with
  | O => None
  | S f =>
      let fix dlist (xs : list sexp) : option (list cexpr) :=
        match xs with
        | [] => Some []
        | y :: ys =>
            match denote_raw mrv f y, dlist ys with
            | Some c, Some cs => Some (c :: cs)
            | _, _ => None
            end
        end in
      let dclause (c : sexp) : option (list string * cexpr) :=
        match c with
        | Lst [Atom kw; Lst xs; n; body] =>
            if String.eqb kw "clause" then
              match uvars xs, nat_of_atom n, denote_raw mrv f body with
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
        | Lst (Atom kw :: info :: cs) =>
            if String.eqb kw "case-lambda" && lambda_info_ok info (map clause_iface cs)
            then dclauses cs else None
        | _ => None
        end in
      let fix dbinds (bs : list sexp) : option (list (string * cexpr)) :=
        match bs with
        | [] => Some []
        | Lst [v; e] :: r =>
            match is_uvar_atom v, denote_raw mrv f e, dbinds r with
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
      let app (info g : sexp) (args : list sexp) : option cexpr :=
        if call_info_ok info (is_primref g) then
          match denote_raw mrv f g, dlist args with
          | Some g', Some a' => Some (CCall g' a')
          | _, _ => None
          end
        else None in
      match x with
      | Atom _ => option_map CVar (is_uvar_atom x)
      | Rec _ => if is_primref x then Some (CPrim x) else None
      | Lst (Atom kw :: rest) =>
          if String.eqb kw "quote" then
            match rest with [d] => Some (CQuote d) | _ => None end
          else if String.eqb kw "case-lambda" then option_map CLam (dlam x)
          else if String.eqb kw "if" then
            match rest with
            | [a; b; c] =>
                match denote_raw mrv f a, denote_raw mrv f b, denote_raw mrv f c with
                | Some a', Some b', Some c' => Some (CIf a' b' c')
                | _, _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "seq" then
            match rest with
            | [a; b] =>
                match denote_raw mrv f a, denote_raw mrv f b with
                | Some a', Some b' => Some (CSeq a' b')
                | _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "let" then
            match rest with
            | [Lst bs; body] =>
                match dbinds bs, denote_raw mrv f body with
                | Some b, Some c => Some (CLet b c)
                | _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "letrec" then
            match rest with
            | [Lst bs; body] =>
                match drecbinds bs, denote_raw mrv f body with
                | Some b, Some c => Some (CLetrec b c)
                | _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "call" then
            if mrv then
              match rest with
              | info :: Atom m :: g :: args => if String.eqb m "#f" then app info g args else None
              | _ => None
              end
            else
              match rest with
              | info :: g :: args => app info g args
              | _ => None
              end
          else None
      | _ => None
      end
  end.

Definition denote_raw_program (mrv : bool) (x : sexp) : option cexpr :=
  match expand_graph x with
  | Some y =>
      match y with
      | Lst (Atom kw :: _) => if String.eqb kw "case-lambda" then denote_raw mrv denote_fuel y else None
      | _ => None
      end
  | None => None
  end.

Definition sem_raw (mrv : bool) {World} prim order truthy (fuel : nat) (x : sexp) (w : World)
  : option (option (value * World)) :=
  option_map (fun c => eval World prim order truthy fuel [] (CCall c []) w) (denote_raw_program mrv x).

Notation check_raw m1 m2 input output :=
  (same_some (denote_raw_program m1 input) (denote_raw_program m2 output)) (only parsing).

(* Universal theorem: a raw pair the checker accepts has one denotation and,
   for every primitive semantics, evaluation-order policy, truthiness, fuel
   and world, the same result. *)
Theorem check_raw_sound :
  forall m1 m2 input output,
    check_raw m1 m2 input output = true ->
    (exists c, denote_raw_program m1 input = Some c /\ denote_raw_program m2 output = Some c) /\
    forall (World : Type) (prim : sexp -> list value -> World -> option (value * World))
      (order : nat -> list nat) (truthy : value -> bool) (fuel : nat) (w : World),
      sem_raw m1 prim order truthy fuel input w = sem_raw m2 prim order truthy fuel output w /\
      sem_raw m1 prim order truthy fuel input w <> None.
Proof.
  intros m1 m2 input output H.
  destruct (same_denotation _ _ H) as [c [Ha Hb]].
  split.
  - exists c; split; assumption.
  - intros World prim order truthy fuel w.
    unfold sem_raw. rewrite Ha, Hb.
    split; [reflexivity | discriminate].
Qed.

(* ---- np-suppress-procedure-checks (L4 -> L4), now with info -------------- *)

Definition raw_or_nil (o : option sexp) : sexp := match o with Some x => x | None => Lst [] end.

Definition suppress_input : sexp := raw_or_nil (raw_datum "np-sanitize-bindings").
Definition suppress_output : sexp := raw_or_nil (raw_datum "np-suppress-procedure-checks").

(* Ground derivations.  The pass changed the raw form (both calls'
   check?= #t became #f; nothing else), the checker accepts the pair, and the
   raw reading agrees with Wave C's reading of the printed form. *)
Theorem suppress_raw_changed : sexp_eqb suppress_input suppress_output = false.
Proof. vm_compute. reflexivity. Qed.

Theorem suppress_raw_checked : check_raw false false suppress_input suppress_output = true.
Proof. vm_compute. reflexivity. Qed.

Theorem suppress_raw_preserves :
  forall (World : Type) (prim : sexp -> list value -> World -> option (value * World))
    (order : nat -> list nat) (truthy : value -> bool) (fuel : nat) (w : World),
    sem_raw false prim order truthy fuel suppress_input w =
    sem_raw false prim order truthy fuel suppress_output w.
Proof. intros. apply (proj2 (check_raw_sound _ _ _ _ suppress_raw_checked)). Qed.

Theorem suppress_raw_matches_printed :
  denote_raw_program false suppress_output =
  denote_program false (datum_or_nil (raw_pretty_datum "np-suppress-procedure-checks")).
Proof. vm_compute. reflexivity. Qed.

(* ---- np-recognize-mrvs (L4 -> L4.5) on the raw form ---------------------- *)

Definition mrvs_raw_output : sexp := raw_or_nil (raw_datum "np-recognize-mrvs").

Theorem mrvs_raw_checked : check_raw false true suppress_output mrvs_raw_output = true.
Proof. vm_compute. reflexivity. Qed.

(* The raw denotation is not vacuous: it rejects the pass input paired with
   a later output and a swapped pair, and it rejects check?= #f on a call
   whose operator is a variable while it accepts the same call with
   check?= #t. *)
Definition var_call (chk : string) : sexp :=
  Lst [Atom "case-lambda";
       Rec [Atom "info:info-lambda"; Atom "src="; Atom "#f"; Atom "sexpr="; Atom "#f";
            Atom "libspec="; Atom "#f"; Atom "interface*="; Lst [Atom "1"]; Atom "dcl*="; Lst [];
            Atom "flags="; Atom "0"; Atom "fv*="; Lst []; Atom "name="; Atom "#f";
            Atom "well-known?="; Atom "#f"; Atom "closure-rep="; Atom "closure";
            Atom "ctci="; Atom "#f"; Atom "pinfo*="; Lst []; Atom "seqno="; Atom "0"];
       Lst [Atom "clause"; Lst [Atom "f.1"]; Atom "1";
            Lst [Atom "call";
                 Rec [Atom "info:info-call"; Atom "src="; Atom "#f"; Atom "sexpr="; Atom "#f";
                      Atom "check?="; Atom chk; Atom "pariah?="; Atom "#f"; Atom "error?="; Atom "#f";
                      Atom "shift-attachment?="; Atom "#f"; Atom "shift-consumer-attachment?*="; Lst []];
                 Atom "f.1"]]].

Theorem raw_rejects_wrong_pairs :
  check_raw false false suppress_input (raw_or_nil (raw_datum "np-name-anonymous-lambda")) = false /\
  check_raw false true mrvs_raw_output suppress_output = false /\
  denote_raw_program false (var_call "#f") = None /\
  denote_raw_program false (var_call "#t") =
    Some (CLam [(["f.1"], CCall (CVar "f.1") [])]).
Proof. vm_compute. repeat split; reflexivity. Qed.
