(* E2E-22: nanopass define-language forms as data, and extends resolution.

   [resolve_all] follows the nanopass framework shipped in csv10.3.0
   (nanopass/nanopass/language.ss, sha256 47761671...): parse-clauses,
   partition-terms, freshen-tspecs, add-tspecs, partition-ntspecs,
   freshen-ntspecs and add-ntspecs, including their list orders.  Terminal
   specs match on type and meta-variables; productions match on syntax only
   (the unparse form after => is ignored); a nonterminal whose productions
   are all removed disappears.  Any form this file does not model (-> pretty
   procedures, prefix => forms, an unknown base language, removing something
   absent, adding a duplicate) makes resolution fail with None. *)
From Coq Require Import String List Bool Arith.
From Buri Require Import ChezNpReader.
Import ListNotations.
Open Scope string_scope.

Definition tspec : Type := (string * list string * option sexp)%type.
Definition alt : Type := (sexp * option sexp)%type.
Definition ntspec : Type := (string * list string * list alt)%type.

Record grammar : Type := mkGrammar {
  g_entry : string;
  g_terminals : list tspec;
  g_nonterminals : list ntspec
}.

Definition atoms (xs : list sexp) : option (list string) :=
  fold_right (fun x acc =>
    match x, acc with Atom a, Some r => Some (a :: r) | _, _ => None end) (Some []) xs.

(* --- parse-terms / parse-alts (infix => only) -------------------------- *)
Fixpoint parse_terms (xs : list sexp) : option (list tspec) :=
  match xs with
  | [] => Some []
  | Lst [Atom t; Lst ms] :: Atom "=>" :: h :: rest =>
      match atoms ms, parse_terms rest with
      | Some ms', Some r => Some ((t, ms', Some h) :: r)
      | _, _ => None
      end
  | Lst [Atom t; Lst ms] :: rest =>
      match atoms ms, parse_terms rest with
      | Some ms', Some r => Some ((t, ms', None) :: r)
      | _, _ => None
      end
  | _ => None
  end.

Definition is_arrow (x : sexp) : bool :=
  match x with Atom "=>" | Atom "->" => true | _ => false end.

Fixpoint parse_alts (xs : list sexp) : option (list alt) :=
  match xs with
  | [] => Some []
  | a :: Atom "=>" :: p :: rest =>
      if is_arrow a then None
      else option_map (cons (a, Some p)) (parse_alts rest)
  | a :: rest =>
      match a with
      | Lst (Atom "=>" :: _) | Lst (Atom "->" :: _) => None
      | _ => if is_arrow a then None else option_map (cons (a, None)) (parse_alts rest)
      end
  end.

(* --- language clauses --------------------------------------------------- *)
Record langdef : Type := mkLangdef {
  ld_name : string;
  ld_base : option string;
  ld_entry : option string;
  ld_terms : list sexp;                              (* raw terminal items *)
  ld_nts : list (string * list string * list sexp)   (* raw nonterminal clauses *)
}.

Fixpoint parse_clauses (cs : list sexp) (base entry : option string)
    (terms : list sexp) (nts : list (string * list string * list sexp))
  : option (option string * option string * list sexp * list (string * list string * list sexp)) :=
  match cs with
  | [] => Some (base, entry, terms, rev nts)
  | Lst [Atom "nongenerative-id"; _] :: rest => parse_clauses rest base entry terms nts
  | Lst [Atom "extends"; Atom b] :: rest =>
      match base with
      | None => parse_clauses rest (Some b) entry terms nts
      | Some _ => None
      end
  | Lst [Atom "entry"; Atom e] :: rest =>
      match entry with
      | None => parse_clauses rest base (Some e) terms nts
      | Some _ => None
      end
  | Lst (Atom "terminals" :: ts) :: rest => parse_clauses rest base entry (app terms ts) nts
  | Lst (Atom nt :: Lst ms :: a :: alts) :: rest =>
      match atoms ms with
      | Some ms' => parse_clauses rest base entry terms ((nt, ms', a :: alts) :: nts)
      | None => None
      end
  | _ => None
  end.

Definition langdef_of (x : sexp) : option langdef :=
  match x with
  | Lst (Atom "define-language" :: Atom name :: cs) =>
      match parse_clauses cs None None [] [] with
      | Some (b, e, ts, nts) => Some (mkLangdef name b e ts nts)
      | None => None
      end
  | _ => None
  end.

(* --- extends ------------------------------------------------------------ *)
Definition tspec_eqb (a b : tspec) : bool :=
  match a, b with
  | (t1, m1, _), (t2, m2, _) =>
      String.eqb t1 t2 && (if list_eq_dec string_dec m1 m2 then true else false)
  end.

Definition alt_eqb (a b : alt) : bool := sexp_eqb (fst a) (fst b).

(* freshen-objects: keep members not matched by a removal; every removal must
   match exactly once. *)
Fixpoint remove_first {A} (eqb : A -> A -> bool) (x : A) (ys : list A) : option (list A) :=
  match ys with
  | [] => None
  | y :: r => if eqb x y then Some r else option_map (cons y) (remove_first eqb x r)
  end.

Fixpoint freshen {A} (eqb : A -> A -> bool) (os rem : list A) : option (list A) :=
  match os with
  | [] => match rem with [] => Some [] | _ => None end
  | o :: r =>
      match remove_first eqb o rem with
      | Some rem' => freshen eqb r rem'
      | None => option_map (cons o) (freshen eqb r rem)
      end
  end.

(* add-objects: prepend one at a time, rejecting duplicates. *)
Fixpoint add_objs {A} (eqb : A -> A -> bool) (os adds : list A) : option (list A) :=
  match adds with
  | [] => Some os
  | a :: r => if existsb (eqb a) os then None else add_objs eqb (a :: os) r
  end.

Fixpoint split_groups (gs : list sexp) : option (list sexp * list sexp) :=
  match gs with
  | [] => Some ([], [])
  | Lst (Atom "+" :: xs) :: r =>
      match split_groups r with Some (p, m) => Some (app xs p, m) | None => None end
  | Lst (Atom "-" :: xs) :: r =>
      match split_groups r with Some (p, m) => Some (p, app xs m) | None => None end
  | _ => None
  end.

(* partition-ntspecs: lists come back reversed, as in nanopass. *)
Fixpoint partition_nts (nts : list (string * list string * list sexp))
    (plus minus : list ntspec) : option (list ntspec * list ntspec) :=
  match nts with
  | [] => Some (plus, minus)
  | (nm, ms, gs) :: r =>
      match split_groups gs with
      | Some (p, m) =>
          match parse_alts p, parse_alts m with
          | Some ap, Some am =>
              partition_nts r
                (match ap with [] => plus | _ => (nm, ms, ap) :: plus end)
                (match am with [] => minus | _ => (nm, ms, am) :: minus end)
          | _, _ => None
          end
      | None => None
      end
  end.

Fixpoint take_named (nm : string) (xs : list ntspec) : option (ntspec * list ntspec) :=
  match xs with
  | [] => None
  | x :: r =>
      let '(n, _, _) := x in
      if String.eqb n nm then Some (x, r)
      else match take_named nm r with
           | Some (y, r') => Some (y, x :: r')
           | None => None
           end
  end.

(* freshen-ntspecs *)
Fixpoint freshen_nts (base minus : list ntspec) : option (list ntspec) :=
  match base with
  | [] => match minus with [] => Some [] | _ => None end
  | (nm, ms, alts) :: r =>
      match take_named nm minus with
      | None => option_map (cons (nm, ms, alts)) (freshen_nts r minus)
      | Some ((_, ms', rem), minus') =>
          match freshen alt_eqb alts rem with
          | Some [] => freshen_nts r minus'
          | Some kept => option_map (cons (nm, ms', kept)) (freshen_nts r minus')
          | None => None
          end
      end
  end.

(* add-ntspecs *)
Fixpoint add_nts (base plus : list ntspec) : option (list ntspec) :=
  match base with
  | [] => Some plus
  | (nm, ms, alts) :: r =>
      match take_named nm plus with
      | None => option_map (cons (nm, ms, alts)) (add_nts r plus)
      | Some ((_, ms', adds), plus') =>
          match add_objs alt_eqb alts adds with
          | Some alts' => option_map (cons (nm, ms', alts')) (add_nts r plus')
          | None => None
          end
      end
  end.

Definition fresh_nts (nts : list (string * list string * list sexp)) : option (list ntspec) :=
  fold_right (fun x acc =>
    match x, acc with
    | (nm, ms, a), Some r => match parse_alts a with Some a' => Some ((nm, ms, a') :: r) | None => None end
    | _, None => None
    end) (Some []) nts.

Fixpoint lookup_lang (nm : string) (env : list (string * grammar)) : option grammar :=
  match env with
  | [] => None
  | (n, g) :: r => if String.eqb n nm then Some g else lookup_lang nm r
  end.

Definition resolve_one (env : list (string * grammar)) (d : langdef) : option grammar :=
  match ld_base d with
  | None =>
      match parse_terms (ld_terms d), fresh_nts (ld_nts d) with
      | Some ts, Some nts =>
          let entry := match ld_entry d, nts with
                       | Some e, _ => Some e
                       | None, (n, _, _) :: _ => Some n
                       | None, [] => None
                       end in
          match entry with Some e => Some (mkGrammar e ts nts) | None => None end
      | _, _ => None
      end
  | Some b =>
      match lookup_lang b env with
      | None => None
      | Some bg =>
          let entry := match ld_entry d with Some e => e | None => g_entry bg end in
          match split_groups (ld_terms d) with
          | Some (tp, tm) =>
              match parse_terms tp, parse_terms tm with
              | Some tplus, Some tminus =>
                  match freshen tspec_eqb (g_terminals bg) tminus with
                  | Some ts1 =>
                      match add_objs tspec_eqb ts1 tplus, partition_nts (ld_nts d) [] [] with
                      | Some ts2, Some (plus, minus) =>
                          match freshen_nts (g_nonterminals bg) minus with
                          | Some nts1 =>
                              match add_nts nts1 plus with
                              | Some nts2 => Some (mkGrammar entry ts2 nts2)
                              | None => None
                              end
                          | None => None
                          end
                      | _, _ => None
                      end
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      end
  end.

Fixpoint resolve_all_acc (env : list (string * grammar)) (ds : list langdef)
  : option (list (string * grammar)) :=
  match ds with
  | [] => Some (rev env)
  | d :: r =>
      match resolve_one env d with
      | Some g => resolve_all_acc ((ld_name d, g) :: env) r
      | None => None
      end
  end.

Definition resolve_all (ds : list langdef) : option (list (string * grammar)) :=
  resolve_all_acc [] ds.

(* --- locating the forms in the packaged source ------------------------- *)
Definition define_language_marker : string := "(define-language ".

Fixpoint occurrences_from (i : nat) (pat s : string) : list nat :=
  match s with
  | EmptyString => []
  | String _ r =>
      if prefix pat s then i :: occurrences_from (S i) pat r
      else occurrences_from (S i) pat r
  end.

Definition occurrences (pat s : string) : list nat := occurrences_from 0 pat s.

Fixpoint read_forms (src : string) (spans : list (nat * nat)) : option (list langdef) :=
  match spans with
  | [] => Some []
  | (start, len) :: r =>
      let text := substring start len src in
      if prefix define_language_marker text then
        match read_exactly text with
        | Some x =>
            match langdef_of x, read_forms src r with
            | Some d, Some ds => Some (d :: ds)
            | _, _ => None
            end
        | None => None
        end
      else None
  end.

(* Every occurrence of the marker in the file is one packaged span, in order,
   and every span reads as exactly one define-language form. *)
Definition spans_complete (src : string) (spans : list (nat * nat)) : bool :=
  if list_eq_dec Nat.eq_dec (map fst spans) (occurrences define_language_marker src)
  then true else false.

Definition grammars_of_source (src : string) (spans : list (nat * nat))
  : option (list (string * grammar)) :=
  if spans_complete src spans then
    match read_forms src spans with
    | Some ds => resolve_all ds
    | None => None
    end
  else None.
