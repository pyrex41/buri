(* E2E-08 certificate grammar BURI/KL-CONTRACT-1 and its Rocq checker.

   A certificate is inert data. It names the theory (calculus identity), the
   program (a fingerprint of the exact resolved KLambda program it is about),
   the captured evaluator a transported statement refers to, the statement
   (a name and a judgment: partial, total or always), the named host
   contracts it relies on (premises, never trusted), the measures of
   recursive functions, and one derivation skeleton per function body plus
   one for the main expression. Skeleton nodes are rule names of the calculus
   (ContractLogic.deriv/dargs/appj) with sub-skeletons; leaves are SHyp (a
   declared host contract), SPrim (a KLambda primitive contract, discharged by
   ContractPrims.prim_spec_valid/io_spec_valid), SRec (a function of this
   program, discharged by rec_partial/rec_total) and SSide (a named semantic
   side condition, returned as an obligation, never decided here).

   The checker decides only identity binding, declaration discipline, the
   measure discipline of total certificates and the exact rule-to-syntax fit
   of every skeleton. It performs no proof search, no evaluation and no
   loading. What is proved: the universal theorems below about this checker.
   What is open (CONTRACT-CERT-SEM): that an accepted skeleton together with
   proofs of its listed side obligations yields a ContractLogic derivation;
   (CONTRACT-CERT-SHEN): that shen/contract-cert.shen computes this checker
   (sampled agreement only, tests/contracts.shen). The fingerprint is a
   tamper-evidence aid (polynomial hash modulo 2^61-1), not a cryptographic
   commitment. *)
From Coq Require Import List ZArith NArith String Bool Lia DecimalString.
From Buri Require Import Observation KLSyntax KLValue KLSemantics.
Import ListNotations.
Module ContractCert.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.

(* ---------- grammar ---------- *)
Inductive rname :=
 | RVal | RUnbound | RLet | RIf | RType | RDefun | RDefunBad | RTrap | RApp | RApp0 | RCall | RCall0
 | RConseq | RExists | RFrame
 | AjSem | AjCtx | AjPartial | AjLam | AjFrozen.
Definition all_rnames := [RVal; RUnbound; RLet; RIf; RType; RDefun; RDefunBad; RTrap; RApp; RApp0; RCall; RCall0;
 RConseq; RExists; RFrame; AjSem; AjCtx; AjPartial; AjLam; AjFrozen].
Lemma all_rnames_complete : forall r, In r all_rnames.
Proof. destruct r; cbn; tauto. Qed.
Definition rname_text (r : rname) : string := match r with
 | RVal => "r_val" | RUnbound => "r_unbound" | RLet => "r_let" | RIf => "r_if" | RType => "r_type"
 | RDefun => "r_defun" | RDefunBad => "r_defun_bad" | RTrap => "r_trap" | RApp => "r_app" | RApp0 => "r_app0"
 | RCall => "r_call" | RCall0 => "r_call0" | RConseq => "r_conseq" | RExists => "r_exists" | RFrame => "r_frame"
 | AjSem => "aj_sem" | AjCtx => "aj_ctx" | AjPartial => "aj_partial" | AjLam => "aj_lam" | AjFrozen => "aj_frozen" end.

Inductive skel :=
 | SRule (r : rname) (subs : list skel)
 | SHyp (h : text) | SPrim (p : text) | SRec (f : text) | SSide (o : text).
Inductive cmode := CPartial | CTotal | CAlways.
Definition defn := (name * list name * expr)%type.
Record program := Program { p_defs : list defn; p_main : expr }.
Record cert := Cert {
 c_format : text;
 c_theory : text * Z;
 c_program : text * Z;
 c_evaluator : text * Z;
 c_stmt : text * cmode;
 c_hyps : list text;
 c_measures : list (text * text);
 c_bodies : list (text * skel);
 c_main : skel }.
Inductive verdict :=
 | Accepted (stmt : text * cmode) (premises : list text) (prims : list text) (obligations : list text)
 | Rejected (why : text).

(* ---------- canonical serialization and fingerprint ---------- *)
Definition t (s : string) : text := of_string s.
Definition decz (z : Z) : text := dec_text z.
Definition lp (x : text) : text := decz (Z.of_nat (List.length x)) ++ t ":" ++ x.
Fixpoint ser (e : expr) : text := match e with
 | ENum (NInt z) => t "(n " ++ decz z ++ t ")"
 | ENum (NFloat b) => t "(f " ++ decz (Z.of_N b) ++ t ")"
 | EStr s => t "(s " ++ lp s ++ t ")"
 | ESym x => t "(y " ++ lp x ++ t ")"
 | EBool b => if b then t "(b true)" else t "(b false)"
 | ENil => t "(nil)"
 | EVar x => t "(v " ++ lp x ++ t ")"
 | ELam x b => t "(lambda " ++ lp x ++ t " " ++ ser b ++ t ")"
 | ELet x a b => t "(let " ++ lp x ++ t " " ++ ser a ++ t " " ++ ser b ++ t ")"
 | EIf c a b => t "(if " ++ ser c ++ t " " ++ ser a ++ t " " ++ ser b ++ t ")"
 | EAnd a b => t "(and " ++ ser a ++ t " " ++ ser b ++ t ")"
 | EOr a b => t "(or " ++ ser a ++ t " " ++ ser b ++ t ")"
 | ECond cs => t "(cond" ++ (fix go cs := match cs with
     | [] => [] | (c, b) :: cs => t " (" ++ ser c ++ t " " ++ ser b ++ t ")" ++ go cs end) cs ++ t ")"
 | ETrap a h => t "(trap " ++ ser a ++ t " " ++ ser h ++ t ")"
 | EFreeze a => t "(freeze " ++ ser a ++ t ")"
 | EType a => t "(type " ++ ser a ++ t ")"
 | EDefun f ps b => t "(defun " ++ lp f ++ t " (" ++ List.concat (map (fun p => lp p ++ t " ") ps) ++ t ") " ++ ser b ++ t ")"
 | EApp h args => t "(app " ++ ser h ++ (fix go es := match es with [] => [] | a :: es => t " " ++ ser a ++ go es end) args ++ t ")"
 | ECall f args => t "(call " ++ lp f ++ (fix go es := match es with [] => [] | a :: es => t " " ++ ser a ++ go es end) args ++ t ")"
 end.
Definition ser_def (d : defn) : text := match d with
 (f, ps, b) => t "(def " ++ lp f ++ t " (" ++ List.concat (map (fun p => lp p ++ t " ") ps) ++ t ") " ++ ser b ++ t ")" end.
Definition ser_program (p : program) : text :=
 t "(program" ++ List.concat (map (fun d => t " " ++ ser_def d) (p_defs p)) ++ t " (main " ++ ser (p_main p) ++ t "))".
Definition hprime : Z := 2305843009213693951%Z.
Fixpoint lh_go (h : Z) (s : text) : Z := match s with
 | [] => h | c :: s => lh_go (Z.modulo (h * 257 + (Z.of_N c + 1)) hprime) s end.
Definition lh (s : text) : Z := lh_go 7 s.
Definition fingerprint (p : program) : Z := lh (ser_program p).

(* The theory identity: the calculus name and a fingerprint of its rule list. *)
Definition theory_name := t "BURI/KL-CONTRACT-1".
Definition theory_text : text := List.concat (map (fun r => t (rname_text r) ++ t " ") all_rnames).
Definition pinned_theory : text * Z := (theory_name, lh theory_text).
(* The captured evaluator: profile e2e07_klambda and the same polynomial hash
   over the bytes of ports/e2e07-klambda.bits (byte b contributes b + 1).
   tests/contracts.shen recomputes it from the file; it is identity
   evidence, not a theorem. *)
Definition pinned_evaluator : text * Z := (t "e2e07_klambda", 1927390069043521096%Z).
Definition format_name := t "buri-contract-1".

(* ---------- skeleton fit ---------- *)
Fixpoint bodies_of (e : expr) : list expr := match e with
 | ELam _ b | EFreeze b => b :: bodies_of b
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => bodies_of a ++ bodies_of b
 | EIf c a b => bodies_of c ++ bodies_of a ++ bodies_of b
 | EType a | EDefun _ _ a => bodies_of a
 | ECond cs => (fix go cs := match cs with [] => [] | (c, b) :: cs => bodies_of c ++ bodies_of b ++ go cs end) cs
 | EApp h args => bodies_of h ++ (fix go es := match es with [] => [] | a :: es => bodies_of a ++ go es end) args
 | ECall _ args => (fix go es := match es with [] => [] | a :: es => bodies_of a ++ go es end) args
 | _ => [] end.
Definition closure_bodies (p : program) : list expr :=
 flat_map (fun d => match d with (_, _, b) => bodies_of b end) (p_defs p) ++ bodies_of (p_main p).

Definition atomic (e : expr) : bool := match e with
 | ENum _ | EStr _ | ESym _ | EBool _ | ENil | EVar _ | ELam _ _ | EFreeze _ => true | _ => false end.

(* fits bs sk (Some e): sk is a derivation skeleton for expression e;
   fits bs sk None: sk is an application skeleton. Closure application
   skeletons (aj_lam, aj_frozen) must fit the body of a closure of the
   program (bs). Structural rules keep the expression. *)
Fixpoint fits (bs : list expr) (sk : skel) (e : option expr) {struct sk} : bool :=
 match sk with
 | SRule r subs =>
   match r, subs, e with
   | RVal, [], Some e => atomic e
   | RUnbound, [], Some (EVar _) => true
   | RLet, [d1; d2], Some (ELet _ a b) => fits bs d1 (Some a) && fits bs d2 (Some b)
   | RIf, [d1; d2; d3], Some (EIf c a b) => fits bs d1 (Some c) && fits bs d2 (Some a) && fits bs d3 (Some b)
   | RType, [d], Some (EType a) => fits bs d (Some a)
   | (RDefun | RDefunBad), [], Some (EDefun _ _ _) => true
   | RTrap, [d1; d2; d3], Some (ETrap a h) => fits bs d1 (Some a) && fits bs d2 (Some h) && fits bs d3 None
   | RApp, d1 :: d2 :: ds, Some (EApp h (a0 :: args)) =>
       fits bs d1 (Some h) && fits bs d2 None &&
       (fix go ds es := match ds, es with
         | [], [] => true | d :: ds, a :: es => fits bs d (Some a) && go ds es | _, _ => false end) ds (a0 :: args)
   | RApp0, [d1; d2], Some (EApp h []) => fits bs d1 (Some h) && fits bs d2 None
   | RCall, d1 :: ds, Some (ECall _ (a0 :: args)) =>
       fits bs d1 None &&
       (fix go ds es := match ds, es with
         | [], [] => true | d :: ds, a :: es => fits bs d (Some a) && go ds es | _, _ => false end) ds (a0 :: args)
   | RCall0, [d1], Some (ECall _ []) => fits bs d1 None
   | (RConseq | RExists | RFrame), [d], Some e => fits bs d (Some e)
   | AjSem, [SSide _], None => true
   (* a contract leaf, then the named side conditions of its precondition *)
   | AjCtx, (SHyp _ | SPrim _ | SRec _) :: sides, None =>
       forallb (fun x => match x with SSide _ => true | _ => false end) sides
   | AjPartial, [SSide _], None => true
   | AjLam, [d], None => existsb (fun b => fits bs d (Some b)) bs
   | AjFrozen, [d], None => existsb (fun b => fits bs d (Some b)) bs
   | _, _, _ => false end
 | _ => false end.

Fixpoint leaves (sk : skel) : list skel := match sk with
 | SRule _ subs => (fix go l := match l with [] => [] | d :: l => leaves d ++ go l end) subs
 | x => [x] end.
Definition hyps_used (l : list skel) := flat_map (fun x => match x with SHyp h => [h] | _ => [] end) l.
Definition prims_used (l : list skel) := flat_map (fun x => match x with SPrim h => [h] | _ => [] end) l.
Definition recs_used (l : list skel) := flat_map (fun x => match x with SRec h => [h] | _ => [] end) l.
Definition sides_used (l : list skel) := flat_map (fun x => match x with SSide h => [h] | _ => [] end) l.

Definition memb (x : text) (l : list text) : bool := existsb (text_eqb x) l.
Fixpoint dupb (l : list text) : bool := match l with [] => false | x :: l => memb x l || dupb l end.
Definition id_eqb (a b : text * Z) : bool := text_eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
Fixpoint skel_of (f : text) (l : list (text * skel)) : option skel := match l with
 | [] => None | (g, sk) :: l => if text_eqb f g then Some sk else skel_of f l end.
Definition prim_names : list text := map (fun p => of_string (prim_name p)) all_prims.
Definition def_names (p : program) : list text := map (fun d => match d with (f, _, _) => f end) (p_defs p).
Definition all_skels (c : cert) : list skel := c_main c :: map snd (c_bodies c).
Definition body_fits (bs : list expr) (c : cert) (d : defn) : bool := match d with
 (f, _, b) => match skel_of f (c_bodies c) with Some sk => fits bs sk (Some b) | None => false end end.

(* ---------- the checker ---------- *)
Definition check (p : program) (c : cert) : verdict :=
 let L := flat_map leaves (all_skels c) in
 let bs := closure_bodies p in
 if negb (text_eqb (c_format c) format_name) then Rejected (t "unknown-format")
 else if negb (id_eqb (c_theory c) pinned_theory) then Rejected (t "stale-theory")
 else if negb (Z.eqb (snd (c_program c)) (fingerprint p)) then Rejected (t "stale-program")
 else if negb (id_eqb (c_evaluator c) pinned_evaluator) then Rejected (t "stale-evaluator")
 else if dupb (c_hyps c) then Rejected (t "duplicate-hypothesis")
 else if negb (forallb (fun h => memb h (c_hyps c)) (hyps_used L)) then Rejected (t "undeclared-hypothesis")
 else if negb (forallb (fun h => memb h prim_names) (prims_used L)) then Rejected (t "unknown-primitive")
 else if negb (forallb (fun f => memb f (def_names p)) (recs_used L)) then Rejected (t "unknown-recursive-function")
 else if (match snd (c_stmt c) with CTotal => negb (forallb (fun f => memb f (map fst (c_measures c))) (recs_used L)) | _ => false end)
   then Rejected (t "missing-measure")
 else if negb (forallb (body_fits bs c) (p_defs p)) then Rejected (t "body-shape")
 else if negb (fits bs (c_main c) (Some (p_main p))) then Rejected (t "main-shape")
 else Accepted (c_stmt c) (c_hyps c) (prims_used L) (sides_used L).

(* ---------- what an acceptance establishes ---------- *)
Lemma memb_In : forall x l, memb x l = true -> In x l.
Proof.
 intros x l H; unfold memb in H; apply existsb_exists in H as (y & I & E).
 apply text_eqb_eq in E; subst; exact I.
Qed.

Ltac ifs H := repeat match type of H with
 | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; [discriminate H|] end.

Theorem check_identity : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 c_format c = format_name /\ c_theory c = pinned_theory /\ snd (c_program c) = fingerprint p /\
 c_evaluator c = pinned_evaluator /\ st = c_stmt c /\ hs = c_hyps c.
Proof.
 intros p c st hs ps os H. unfold check in H. cbv zeta in H. ifs H. injection H as <- <- _ _.
 repeat match goal with E : negb _ = false |- _ => apply negb_false_iff in E end.
 unfold id_eqb in *. repeat match goal with E : (_ && _)%bool = true |- _ => apply andb_true_iff in E as [? ?] end.
 repeat match goal with E : text_eqb _ _ = true |- _ => apply text_eqb_eq in E | E : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in E end.
 destruct (c_theory c), (c_evaluator c); cbn in *; subst. repeat split; auto.
Qed.

Lemma check_ok : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 let L := flat_map leaves (all_skels c) in
 st = c_stmt c /\ hs = c_hyps c /\ ps = prims_used L /\ os = sides_used L /\
 dupb (c_hyps c) = false /\
 forallb (fun h => memb h (c_hyps c)) (hyps_used L) = true /\
 forallb (fun h => memb h prim_names) (prims_used L) = true /\
 forallb (fun f => memb f (def_names p)) (recs_used L) = true /\
 (snd (c_stmt c) = CTotal -> forallb (fun f => memb f (map fst (c_measures c))) (recs_used L) = true) /\
 forallb (body_fits (closure_bodies p) c) (p_defs p) = true /\
 fits (closure_bodies p) (c_main c) (Some (p_main p)) = true.
Proof.
 intros p c st hs ps os H. unfold check in H. cbv zeta in H. ifs H. injection H as <- <- <- <-. cbv zeta.
 repeat match goal with E : negb _ = false |- _ => apply negb_false_iff in E end.
 repeat split; auto.
 match goal with E : (match snd (c_stmt c) with CTotal => _ | _ => _ end) = false |- _ =>
   intro T; rewrite T in E; apply negb_false_iff in E; exact E end.
Qed.

Lemma In_flat_map_leaf : forall (sel : skel -> list text) x L, In x (flat_map sel L) -> exists y, In y L /\ In x (sel y).
Proof. intros sel x L I; apply in_flat_map in I; exact I. Qed.

(* Every host contract a derivation relies on is a declared premise, and the
   declared premises are exactly what the verdict reports. *)
Theorem check_hyps_declared : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 forall h, In (SHyp h) (flat_map leaves (all_skels c)) -> In h hs.
Proof.
 intros p c st hs ps os H h I. destruct (check_ok p c st hs ps os H) as (_ & -> & _ & _ & _ & Hh & _).
 rewrite forallb_forall in Hh. apply memb_In, Hh. unfold hyps_used. apply in_flat_map. exists (SHyp h); cbn; auto.
Qed.
Theorem check_hyps_distinct : forall p c st hs ps os, check p c = Accepted st hs ps os -> dupb hs = false.
Proof. intros p c st hs ps os H. destruct (check_ok p c st hs ps os H) as (_ & -> & _ & _ & D & _). exact D. Qed.
(* Primitive leaves name KLambda primitives only (their contracts are the
   proved ContractPrims ones); recursive leaves name functions of the program. *)
Theorem check_prims_known : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 forall q, In (SPrim q) (flat_map leaves (all_skels c)) -> In q prim_names.
Proof.
 intros p c st hs ps os H q I. destruct (check_ok p c st hs ps os H) as (_ & _ & _ & _ & _ & _ & Hp & _).
 rewrite forallb_forall in Hp. apply memb_In, Hp. apply in_flat_map. exists (SPrim q); cbn; auto.
Qed.
Theorem check_recs_defined : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 forall f, In (SRec f) (flat_map leaves (all_skels c)) -> In f (def_names p).
Proof.
 intros p c st hs ps os H f I. destruct (check_ok p c st hs ps os H) as (_ & _ & _ & _ & _ & _ & _ & Hr & _).
 rewrite forallb_forall in Hr. apply memb_In, Hr. apply in_flat_map. exists (SRec f); cbn; auto.
Qed.
(* A total-correctness certificate carries a measure for every recursive
   function it relies on (rec_total); a partial one need not (rec_partial). *)
Theorem check_total_measures : forall p c st hs ps os, check p c = Accepted st hs ps os -> snd st = CTotal ->
 forall f, In (SRec f) (flat_map leaves (all_skels c)) -> In f (map fst (c_measures c)).
Proof.
 intros p c st hs ps os H T f I. destruct (check_ok p c st hs ps os H) as (-> & _ & _ & _ & _ & _ & _ & _ & Hm & _).
 specialize (Hm T). rewrite forallb_forall in Hm. apply memb_In, Hm. apply in_flat_map. exists (SRec f); cbn; auto.
Qed.
Theorem check_shapes : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 fits (closure_bodies p) (c_main c) (Some (p_main p)) = true /\
 forall f params b, In (f, params, b) (p_defs p) ->
   exists sk, skel_of f (c_bodies c) = Some sk /\ fits (closure_bodies p) sk (Some b) = true.
Proof.
 intros p c st hs ps os H. destruct (check_ok p c st hs ps os H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & Hm).
 split; [exact Hm|]. intros f params b I. rewrite forallb_forall in Hb. specialize (Hb _ I). cbn in Hb.
 destruct (skel_of f (c_bodies c)) as [sk|]; [eauto|discriminate].
Qed.
(* The residual obligations are exactly the side-condition leaves; nothing
   is decided about them here. *)
Theorem check_obligations : forall p c st hs ps os, check p c = Accepted st hs ps os ->
 os = sides_used (flat_map leaves (all_skels c)) /\ ps = prims_used (flat_map leaves (all_skels c)).
Proof. intros p c st hs ps os H. destruct (check_ok p c st hs ps os H) as (_ & _ & Hp & Ho & _). auto. Qed.

(* Stale or foreign certificates never grant acceptance. *)
Theorem stale_program_rejected : forall p c, snd (c_program c) <> fingerprint p ->
 forall st hs ps os, check p c <> Accepted st hs ps os.
Proof. intros p c N st hs ps os H. apply N. exact (proj1 (proj2 (proj2 (check_identity p c st hs ps os H)))). Qed.
Theorem stale_theory_rejected : forall p c, c_theory c <> pinned_theory ->
 forall st hs ps os, check p c <> Accepted st hs ps os.
Proof. intros p c N st hs ps os H. apply N. exact (proj1 (proj2 (check_identity p c st hs ps os H))). Qed.
Theorem stale_evaluator_rejected : forall p c, c_evaluator c <> pinned_evaluator ->
 forall st hs ps os, check p c <> Accepted st hs ps os.
Proof. intros p c N st hs ps os H. apply N. exact (proj1 (proj2 (proj2 (proj2 (check_identity p c st hs ps os H))))). Qed.

(* Rule-to-syntax fit: a rule node fits only the expression form of the
   conclusion of the ContractLogic constructor of the same name; application
   rules never fit an expression. *)
Definition rule_shape (r : rname) (e : expr) : Prop := match r with
 | RVal => atomic e = true
 | RUnbound => exists x, e = EVar x
 | RLet => exists x a b, e = ELet x a b
 | RIf => exists c a b, e = EIf c a b
 | RType => exists a, e = EType a
 | RDefun | RDefunBad => exists f ps b, e = EDefun f ps b
 | RTrap => exists a h, e = ETrap a h
 | RApp => exists h a args, e = EApp h (a :: args)
 | RApp0 => exists h, e = EApp h []
 | RCall => exists f a args, e = ECall f (a :: args)
 | RCall0 => exists f, e = ECall f []
 | RConseq | RExists | RFrame => True
 | AjSem | AjCtx | AjPartial | AjLam | AjFrozen => False end.
Theorem fits_rule_shape : forall bs r subs e, fits bs (SRule r subs) (Some e) = true -> rule_shape r e.
Proof.
 intros bs r subs e H. destruct r; cbn [rule_shape];
 destruct subs as [|d1 [|d2 [|d3 ds]]]; destruct e; cbn [fits] in H; try discriminate;
 try (destruct args as [|a0 args]; cbn [fits] in H; try discriminate);
 try (destruct ds; cbn [fits] in H; try discriminate);
 eauto 7; destruct d1; cbn [fits] in H; discriminate.
Qed.
End ContractCert.
