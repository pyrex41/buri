(* Port-fix lane: the PATCHED Shen-CL lowering definitions.

   Source: Shen-CL 4844072d src/compiler.shen (blob 2d624377) with
   ports/patches/shen-cl-compiler.diff applied (patched blob 60522d09,
   packaging by scripts/package-patched.py, inert capture by
   shen/cl-lowering-patch-capture.shen into CLLoweringPatchCapture.v).
   This is NOT the stock port: CLLowering.v and its qsafe-conditioned
   theorems are unchanged and still describe stock Shen-CL.

   Two patches:
   - optimise-boolean-check: the EQ rewrite of (shen-cl.equal? X 'S) is
     guarded by (symbol? S). Theorem [patched_optimise_sound] has NO qsafe
     premise: the rewrite is exact on its whole input domain.
   - emit-cond-clauses: an empty clause list emits a final (T <compiled
     (simple-error "condition failure")>) clause. Theorem
     [patched_cond_final_t]: every emitted CL cond ends in a T clause, and
     when no source test is literally true that clause's body is the
     compiled (simple-error "condition failure").

   Model, as in CLLowering: the admitted ASTs are interpreted; compile-
   expression is an arbitrary function. Shen's symbol? is an arbitrary
   oracle [sym] constrained only by soundness (an answer true is given only
   for a symbol; kernel symbol? answers false on booleans, numbers, strings,
   conses, () and vectors), so no symbol spelling rule is guessed. The
   interpreter extends CLLowering's with Shen let (sequential, lexical) and
   that symbol? oracle; everything else is CLLowering.apply_builtin. *)
From Coq Require Import String List Bool Ascii Arith.
From Buri Require Import CLLowering CLWrappers.
Import ListNotations.
Open Scope string_scope.
Arguments String.eqb : simpl nomatch.

(* ---------- 1. Reviewed expected ASTs of the patched definitions ---------- *)
Definition sym_guard := P [A "and"; P [A "="; cl_ "quote"; A "Quote"]; P [A "symbol?"; A "S"]].
Definition expected_optimise_p := P ([A "define"; A "optimise-boolean-check";
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
   A "where"; sym_guard;
 equal2 (B [A "Quote"; A "S"]) (A "X"); A "->"; B [cl_ "eq"; A "X"; B [A "Quote"; A "S"]];
   A "where"; sym_guard;
 equal2 (A "X") (A "Y"); A "->"; B [kl_ "absequal"; A "X"; A "Y"];
 B [A "greater?"; A "X"; A "Y"]; A "->"; B [cl_ ">"; A "X"; A "Y"];
 B [A "greater-than-or-equal-to?"; A "X"; A "Y"]; A "->"; B [cl_ ">="; A "X"; A "Y"];
 B [A "less?"; A "X"; A "Y"]; A "->"; B [cl_ "<"; A "X"; A "Y"];
 B [A "less-than-or-equal-to?"; A "X"; A "Y"]; A "->"; B [cl_ "<="; A "X"; A "Y"];
 B [A "Quote"; A "true"]; A "->"; cl_ "t"; A "where"; is_ "Quote" "quote";
 B [A "Quote"; A "false"]; A "->"; cl_ "nil"; A "where"; is_ "Quote" "quote";
 A "Exp"; A "->"; B [A "true?"; A "Exp"]]).
Definition expected_emit_cond := P [A "define"; A "emit-cond";
 A "Clauses"; A "Scope"; A "->"; B [cl_ "cond"; SBar; P [A "emit-cond-clauses"; A "Clauses"; A "Scope"]]].
Definition cond_general := [
 B [B [A "false"; A "_"]; SBar; A "Rest"]; A "Scope"; A "->"; P [A "emit-cond-clauses"; A "Rest"; A "Scope"];
 B [B [A "true"; A "Body"]; SBar; A "_"]; A "Scope"; A "->"; B [B [cl_ "t"; ce_ "Body"]];
 B [B [A "Test"; A "Body"]; SBar; A "Rest"]; A "Scope";
 A "->"; P [A "let"; A "CompiledTest"; P [A "optimise-boolean-check"; ce_ "Test"];
            A "CompiledBody"; ce_ "Body";
            A "CompiledRest"; P [A "emit-cond-clauses"; A "Rest"; A "Scope"];
            B [B [A "CompiledTest"; A "CompiledBody"]; SBar; A "CompiledRest"]]].
Definition expected_emit_cond_clauses_p := P ([A "define"; A "emit-cond-clauses";
 B []; A "Scope"; A "->"; B [B [cl_ "t"; P [A "compile-expression"; B [A "simple-error"; SStr "condition failure"]; A "Scope"]]]]
 ++ cond_general).
Definition expected_emit_cond_clauses_stock := P ([A "define"; A "emit-cond-clauses";
 B []; A "_"; A "->"; B []] ++ cond_general).

(* Symbols occurring in the patched definitions that Shen 43.1's
   (get shen external-symbols) contains (reviewed against the kernel
   declarations; the capture records the capture host's answer). *)
Definition reviewed_sysfuncs_p : list string :=
 ["define"; "true"; "false"; "->"; "where"; "and"; "="; "if"; "or"; "let";
  "cons?"; "string?"; "number?"; "empty?"; "null"; "not"; "fail"; "symbol?";
  ">"; ">="; "<"; "<="; "cond"; "simple-error"; "_"].

Record patch_source := mk_patch_source {
 ps_package : src; ps_optimise : src; ps_sequence : src; ps_emit_cond : src;
 ps_emit_cond_clauses : src; ps_stock_cond : src; ps_sysfuncs : list string }.
Definition admitted_patch (L : patch_source) : bool :=
 src_eqb (ps_package L) expected_package && src_eqb (ps_optimise L) expected_optimise_p
 && src_eqb (ps_sequence L) expected_sequence && src_eqb (ps_emit_cond L) expected_emit_cond
 && src_eqb (ps_emit_cond_clauses L) expected_emit_cond_clauses_p
 && src_eqb (ps_stock_cond L) expected_emit_cond_clauses_stock
 && set_eqb (ps_sysfuncs L) reviewed_sysfuncs_p.
Lemma patch_admission_exact : forall L, admitted_patch L = true ->
 ps_package L = expected_package /\ ps_optimise L = expected_optimise_p /\ ps_sequence L = expected_sequence /\
 ps_emit_cond L = expected_emit_cond /\ ps_emit_cond_clauses L = expected_emit_cond_clauses_p /\
 ps_stock_cond L = expected_emit_cond_clauses_stock.
Proof.
 intros L H. unfold admitted_patch in H.
 repeat (apply andb_true_iff in H as [H ?]).
 repeat split; apply src_eqb_sound; assumption.
Qed.

(* Package resolution as in CLLowering, with the reviewed table above. *)
Definition internal_p (p : string) (ext : list string) (s : string) : bool :=
 negb (mem s ext) && negb (sng s) && negb (dbl s)
 && negb (mem s reviewed_sysfuncs_p || String.prefix "lisp." s) && negb (is_variable s)
 && negb (String.prefix "shen." s) && negb (String.prefix (p ++ ".") s).
Definition resolve_p (p : string) (ext : list string) (s : string) : string :=
 if internal_p p ext s then p ++ "." ++ s else s.
Definition ECOND := "shen-cl.emit-cond".
Definition ECC := "shen-cl.emit-cond-clauses".
Definition compile_patch (L : patch_source) : option (defs * defs) :=
 match package_of (ps_package L) with
 | Some (p, ext) =>
   let r := resolve_p p ext in
   match define_of r (ps_optimise L), define_of r (ps_sequence L), define_of r (ps_emit_cond L),
         define_of r (ps_emit_cond_clauses L), define_of r (ps_stock_cond L) with
   | Some d1, Some d2, Some d3, Some d4, Some d5 =>
     if String.eqb (fst d1) OPT && String.eqb (fst d2) SEQ && String.eqb (fst d3) ECOND
        && String.eqb (fst d4) ECC && String.eqb (fst d5) ECC
     then Some ([d1; d2; d3; d4], [d5]) else None
   | _, _, _, _, _ => None end
 | None => None end.
Definition expected_patch := mk_patch_source expected_package expected_optimise_p expected_sequence
 expected_emit_cond expected_emit_cond_clauses_p expected_emit_cond_clauses_stock reviewed_sysfuncs_p.
Definition expected_pair : defs * defs :=
 Eval vm_compute in match compile_patch expected_patch with Some d => d | None => ([], []) end.
Definition patched_defs := fst expected_pair.
Definition stock_cond_defs := snd expected_pair.
Lemma compile_expected_patch : compile_patch expected_patch = Some expected_pair.
Proof. vm_compute. reflexivity. Qed.
Definition patch_defs (L : patch_source) : defs * defs :=
 match compile_patch L with Some d => d | None => ([], []) end.
Lemma admitted_patch_defs : forall L, admitted_patch L = true -> patch_defs L = expected_pair.
Proof.
 intros L H. destruct (patch_admission_exact L H) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
 unfold patch_defs, compile_patch. rewrite H1, H2, H3, H4, H5, H6.
 change (match compile_patch expected_patch with Some d => d | None => ([], []) end = expected_pair).
 rewrite compile_expected_patch. reflexivity.
Qed.

(* ---------- 2. Interpreter: CLLowering's, plus Shen let and a symbol? oracle ---------- *)
Section Eval.
Variable sym : sv -> bool.
Variable call : string -> list sv -> lres.
Definition builtin_p (f : string) (vals : list sv) : lres :=
 if String.eqb f "symbol?" then match vals with [v] => LOk (shen_bool (sym v)) | _ => LUnsupported end
 else apply_builtin call f vals.
Fixpoint eval_p (s : binding) (e : expr) : lres :=
 match e with
 | EVar x => match lookup x s with Some v => LOk v | None => LUnsupported end
 | EConst v => LOk v
 | ECons a b => match eval_p s a with
   | LOk x => match eval_p s b with LOk y => LOk (VCons x y) | r => r end
   | r => r end
 | EApp f args =>
   if String.eqb f "let" then
     (fix lets (s : binding) (l : list expr) : lres := match l with
      | [b] => eval_p s b
      | EVar x :: a :: rest => match eval_p s a with LOk v => lets ((x, v) :: s) rest | r => r end
      | _ => LUnsupported end) s args
   else if String.eqb f "and" || String.eqb f "or" then
     match args with
     | [a; b] => match eval_p s a with
       | LOk x => if is_true x then (if String.eqb f "or" then LOk x else
                      match eval_p s b with LOk y => if is_true y || is_false y then LOk y else LUnsupported | r => r end)
                  else if is_false x then (if String.eqb f "and" then LOk x else
                      match eval_p s b with LOk y => if is_true y || is_false y then LOk y else LUnsupported | r => r end)
                  else LUnsupported
       | r => r end
     | _ => LUnsupported end
   else
   match (fix go (l : list expr) : sum (list sv) lres :=
            match l with [] => inl []
            | a :: r => match eval_p s a with
              | LOk v => match go r with inl vs => inl (v :: vs) | inr x => inr x end
              | x => inr x end end) args with
   | inl vals => builtin_p f vals
   | inr x => x end
 end.
Fixpoint apply_clauses_p (cs : list clause) (vals : list sv) : lres :=
 match cs with
 | [] => LNoMatch
 | c :: rest => match match_pats (c_pats c) vals [] with
   | MNo => apply_clauses_p rest vals
   | MUnsup => LUnsupported
   | MOk s => match c_guard c with
     | None => eval_p s (c_rhs c)
     | Some g => match eval_p s g with
       | LOk v => if is_true v then eval_p s (c_rhs c)
                  else if is_false v then apply_clauses_p rest vals else LUnsupported
       | x => x end end end end.
Definition guard_holds_p (s : binding) (g : option expr) : Prop :=
 match g with None => True | Some g => exists v, eval_p s g = LOk v /\ is_true v = true end.
Lemma apply_clauses_p_sound : forall cs vals r, apply_clauses_p cs vals = LOk r ->
 exists c s, In c cs /\ match_pats (c_pats c) vals [] = MOk s /\ guard_holds_p s (c_guard c)
   /\ eval_p s (c_rhs c) = LOk r.
Proof.
 intros cs vals r. induction cs as [|c cs IH]; simpl; intros H; [discriminate|].
 destruct (match_pats (c_pats c) vals []) eqn:Hm; try discriminate.
 - destruct (c_guard c) as [g|] eqn:Hg.
   + destruct (eval_p s g) eqn:He; try discriminate.
     destruct (is_true v) eqn:Ht.
     * exists c, s. repeat split; auto. rewrite Hg. simpl. eauto.
     * destruct (is_false v); try discriminate. destruct (IH H) as [c' [s' [? ?]]]. exists c', s'. tauto.
   + exists c, s. repeat split; auto. rewrite Hg. simpl. exact I.
 - destruct (IH H) as [c' [s' [? ?]]]. exists c', s'. tauto.
Qed.
End Eval.

Fixpoint run_p (sym : sv -> bool) (fuel : nat) (Ds : defs) (ce : sv -> sv -> lres) (f : string) (vals : list sv) : lres :=
 match fuel with
 | O => LFuel
 | S n => match assoc f Ds with
   | Some cs => apply_clauses_p sym (fun g vs => if String.eqb g CE then
                    match vs with [a; b] => ce a b | _ => LUnsupported end
                  else run_p sym n Ds ce g vs) cs vals
   | None => LUnsupported end end.
Definition callf_p sym n ce : string -> list sv -> lres :=
 fun g vs => if String.eqb g CE then match vs with [a; b] => ce a b | _ => LUnsupported end
             else run_p sym n patched_defs ce g vs.

Definition opt_clauses_p : list clause := Eval vm_compute in
 match assoc OPT patched_defs with Some cs => cs | None => [] end.
Definition seq_clauses_p : list clause := Eval vm_compute in
 match assoc SEQ patched_defs with Some cs => cs | None => [] end.
Definition ecc_clauses_p : list clause := Eval vm_compute in
 match assoc ECC patched_defs with Some cs => cs | None => [] end.
Definition ecc_clauses_stock : list clause := Eval vm_compute in
 match assoc ECC stock_cond_defs with Some cs => cs | None => [] end.
Lemma assoc_opt_p : assoc OPT patched_defs = Some opt_clauses_p. Proof. vm_compute. reflexivity. Qed.
Lemma assoc_seq_p : assoc SEQ patched_defs = Some seq_clauses_p. Proof. vm_compute. reflexivity. Qed.
Lemma assoc_ecc_p : assoc ECC patched_defs = Some ecc_clauses_p. Proof. vm_compute. reflexivity. Qed.
Lemma run_p_S : forall sym n ce f vals, run_p sym (S n) patched_defs ce f vals =
 match assoc f patched_defs with Some cs => apply_clauses_p sym (callf_p sym n ce) cs vals | None => LUnsupported end.
Proof. reflexivity. Qed.

Ltac no_match_inside x := lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end.
(* Destruct only binding lookups and Booleans (as CLLowering.crush2). *)
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
Ltac prep Hg He := unfold callf_p in Hg, He; cbn [c_guard c_rhs c_pats fill] in *; simpl in Hg, He;
 unfold builtin_p, apply_builtin, cl_sym, shen_bool in Hg, He; simpl in Hg, He; norm_up; simpl in Hg, He.

(* ---------- 3. optimise-boolean-check: exact on its whole domain ---------- *)
Section Sound.
Variable St : Type.
Variable prim : string -> list sv -> St -> out St -> Prop.
Variable other : binding -> sv -> St -> out St -> Prop.
Hypothesis C : primitive_contracts St prim.
Variable sym : sv -> bool.
Hypothesis Hsym : forall v, sym v = true -> symbolic v = true.

Ltac use_ih IH := eapply IH; eassumption.
Ltac fn_side := first [reflexivity | (unfold TRUEP; discriminate)].
Ltac opt_finish IHo IHs :=
 first
 [ apply sem_true
 | apply sem_if_tf
 | apply sem_quote_true
 | apply sem_quote_false
 | apply (sem_let St prim other false); use_ih IHo
 | apply (sem_let St prim other true); use_ih IHo
 | apply sem_ifb; use_ih IHo
 | apply sem_and; use_ih IHo
 | apply sem_or; use_ih IHo
 | apply sem_not; [apply (pc_not St prim C) | apply (pc_cl_not St prim C) | use_ih IHo]
 | apply sem_progn; match goal with H : run_p _ _ _ _ _ [?f] = LOk ?r |- _ =>
     let Hs := fresh in destruct (IHs f r H) as [_ [_ Hs]]; exact Hs end
 | apply (sem_null_right St prim other C)
 | apply (sem_null_left St prim other C)
 | apply (sem_fail_left St prim other C)
 | apply (sem_fail_right St prim other C)
 | apply sem_pred; [fn_side|fn_side|fn_side|fn_side|first [apply (pc_cons St prim C)|apply (pc_string St prim C)
     |apply (pc_number St prim C)|apply (pc_empty St prim C)|apply (pc_greater St prim C)|apply (pc_greater_eq St prim C)
     |apply (pc_less St prim C)|apply (pc_less_eq St prim C)|apply (pc_absequal St prim C)]]
 | eapply sem_same2_lit_left; [fn_side|fn_side|fn_side|fn_side|apply pure_str|intros; apply (proj1 (pc_string_equal St prim C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_str|intros; apply (proj2 (pc_string_equal St prim C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_num|intros; apply (proj1 (pc_numeric St prim C _ _))]
 | eapply sem_swap_lit; [fn_side|fn_side|fn_side|fn_side|apply pure_num|intros; apply (proj2 (pc_numeric St prim C _ _))]
 | eapply sem_same2_lit_right; [fn_side|fn_side|fn_side|fn_side|apply pure_quote|
     intros; eapply proj1; eapply (pc_symbol_eq St prim C); apply Hsym; eassumption]
 | eapply sem_swap_lit; [fn_side|fn_side|fn_side|fn_side|apply pure_quote|
     intros; eapply proj2; eapply (pc_symbol_eq St prim C); apply Hsym; eassumption]
 ].

(* For every compile-expression function, every fuel, every input datum (no
   qsafe restriction) and every symbol? oracle that answers true only on
   symbols: whatever the patched optimise-boolean-check returns is
   test-equivalent to its input, in every CL world satisfying
   primitive_contracts. *)
Theorem patched_optimise_sound : forall ce n,
 (forall v r, run_p sym n patched_defs ce OPT [v] = LOk r -> OptEquiv St prim other v r) /\
 (forall v r, run_p sym n patched_defs ce SEQ [v] = LOk r -> seq_ok St prim other v r).
Proof.
 intros ce n. induction n as [|n [IHo IHs]].
 - split; intros; discriminate.
 - split.
   + intros v r H. rewrite run_p_S, assoc_opt_p in H.
     apply apply_clauses_p_sound in H as [c [s [Hin [Hm [Hg He]]]]].
     unfold opt_clauses_p in Hin. simpl in Hin.
     repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end.
     all: apply match_pats1 in Hm; pose proof (match_pat_fill _ _ _ _ Hm eq_refl) as Hv; subst v; clear Hm.
     all: prep Hg He; crush2.
     all: opt_finish IHo IHs.
   + intros v r H. rewrite run_p_S, assoc_seq_p in H.
     apply apply_clauses_p_sound in H as [c [s [Hin [Hm [Hg He]]]]].
     unfold seq_clauses_p in Hin. simpl in Hin.
     repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end.
     all: apply match_pats1 in Hm; pose proof (match_pat_fill _ _ _ _ Hm eq_refl) as Hv; subst v; clear Hm.
     all: prep Hg He; crush2.
     * split; [eauto | split; [eauto | apply sem_seq_one; use_ih IHo]].
     * match goal with H : run_p _ _ _ _ _ [?f] = LOk ?r |- _ =>
         destruct (IHs f r H) as [[a [b ->]] [[c [d ->]] Hs]] end.
       split; [eauto | split; [eauto | apply sem_seq_cons; exact Hs]].
Qed.
End Sound.

(* ---------- 4. emit-cond-clauses: every emitted CL cond ends in a T clause ---------- *)
Module W := CLWrappers.CLWrappers.
Definition cl_err := VCons (VSym "simple-error") (VCons (VStr "condition failure") VNil).
Definition clauses_t (pre : list sv) (fin : sv) := W.SL (pre ++ [W.SL [VSym "T"; fin]]).
Fixpoint no_true_cl (v : sv) : Prop := match v with
 | VNil => True
 | VCons (VCons t (VCons _ VNil)) rest => t <> VSym "true" /\ no_true_cl rest
 | _ => False end.
Definition pair_clause (c : sv) := exists t b, c = W.SL [t; b].

(* For every symbol? oracle, compile-expression function, fuel and source
   clause list: whatever the patched emit-cond-clauses returns is a list of
   two-element clauses followed by a final (T fin) clause, and when no source
   test is literally true, fin is compile-expression's result for
   (simple-error "condition failure"). *)
Theorem patched_cond_final_t : forall sym ce n cs sc r,
 run_p sym n patched_defs ce ECC [cs; sc] = LOk r ->
 exists pre fin, r = clauses_t pre fin /\ Forall pair_clause pre /\ (no_true_cl cs -> ce cl_err sc = LOk fin).
Proof.
 intros sym ce n. induction n as [|n IH]; intros cs sc r H; [discriminate|].
 rewrite run_p_S, assoc_ecc_p in H.
 apply apply_clauses_p_sound in H as [c [s [Hin [Hm [Hg He]]]]].
 unfold ecc_clauses_p in Hin. simpl in Hin.
 repeat match goal with Hin : _ \/ _ |- _ => destruct Hin as [<-|Hin] | Hin : False |- _ => contradiction end;
 simpl in Hm; prep Hg He; crush2.
 - exists [], v. split; [reflexivity|]. split; [constructor|]. intros _. assumption.
 - destruct (IH _ _ _ He) as [pre [fin [-> [F N]]]]. exists pre, fin. split; [reflexivity|]. split; [exact F|].
   intros [_ NT]. exact (N NT).
 - exists [], v. split; [reflexivity|]. split; [constructor|]. intros [NT _]. exfalso; apply NT; reflexivity.
 - match goal with E : run_p _ _ _ _ _ _ = LOk ?cr |- _ => destruct (IH _ _ _ E) as [pre [fin [-> [F N]]]] end.
   eexists (_ :: pre), fin. split; [reflexivity|]. split; [constructor; [eexists _, _; reflexivity|exact F]|].
   intros [_ NT]. exact (N NT).
Qed.

(* Common Lisp COND (CLWrappers' functional model): if every earlier test
   evaluates to NIL, the final T clause fires and the value is its body's. *)
Lemma cond_reaches_t : forall h env m pre fin,
 Forall (fun c => exists t b, c = W.SL [t; b] /\ W.ceval (S (S m)) h env t = W.CRet VNil) pre ->
 W.ceval (S (S (S m))) h env (VCons (VSym "COND") (clauses_t pre fin)) = W.ceval (S (S m)) h env fin.
Proof.
 intros h env m pre fin F. induction F as [|c pre [t [b [-> Ht]]] _ IH].
 - unfold clauses_t. cbn [app]. change (VCons (VSym "COND") (W.SL [W.SL [VSym "T"; fin]]))
     with (W.SL (W.Sy "COND" :: W.SL [VSym "T"; fin] :: [])).
   apply (W.ce_cond_hit h (S (S m)) env (VSym "T") fin [] W.T); reflexivity.
 - unfold clauses_t in *. cbn [app]. change (VCons (VSym "COND") (W.SL (W.SL [t; b] :: pre ++ [W.SL [VSym "T"; fin]])))
     with (W.SL (W.Sy "COND" :: W.SL [t; b] :: pre ++ [W.SL [VSym "T"; fin]])).
   rewrite (W.ce_cond_miss h (S (S m)) env t b _ Ht). exact IH.
Qed.

(* The patched lowering of a cond with no literal-true test, in a CL world
   where every emitted test evaluates to NIL, evaluates exactly as the
   compiled (simple-error "condition failure"): the porting rule
   (cond) = (simple-error "condition failure"). Stock Shen-CL instead emits
   no clause for [] (stock_cond_empty below); CL (COND) is NIL. *)
Theorem patched_cond_profile : forall sym ce n cs sc r fin h env m pre,
 run_p sym n patched_defs ce ECC [cs; sc] = LOk r -> no_true_cl cs -> ce cl_err sc = LOk fin ->
 r = clauses_t pre fin ->
 Forall (fun c => exists t b, c = W.SL [t; b] /\ W.ceval (S (S m)) h env t = W.CRet VNil) pre ->
 W.ceval (S (S (S m))) h env (VCons (VSym "COND") r) = W.ceval (S (S m)) h env fin.
Proof. intros. subst r. apply cond_reaches_t. assumption. Qed.

(* Ground derivations on the captured STOCK emit-cond-clauses, interpreted
   by the same interpreter: [] and [[false 1]] emit no clauses at all. *)
Example stock_cond_empty : forall sym ce sc, run_p sym 3 stock_cond_defs ce ECC [VNil; sc] = LOk VNil.
Proof. reflexivity. Qed.
Example stock_cond_false_only : forall sym ce sc,
 run_p sym 3 stock_cond_defs ce ECC [VCons (VCons (VSym "false") (VCons (VNum "1") VNil)) VNil; sc] = LOk VNil.
Proof. reflexivity. Qed.

(* ---------- 5. Statements about any admitted patched capture ---------- *)
Theorem admitted_patch_optimise_sound : forall L St prim other sym ce n v r,
 admitted_patch L = true -> primitive_contracts St prim -> (forall v, sym v = true -> symbolic v = true) ->
 run_p sym n (fst (patch_defs L)) ce OPT [v] = LOk r -> OptEquiv St prim other v r.
Proof.
 intros L St prim other sym ce n v r HL C Hs H. rewrite admitted_patch_defs in H by exact HL.
 exact (proj1 (patched_optimise_sound St prim other C sym Hs ce n) v r H).
Qed.
Theorem admitted_patch_cond_final_t : forall L sym ce n cs sc r,
 admitted_patch L = true -> run_p sym n (fst (patch_defs L)) ce ECC [cs; sc] = LOk r ->
 exists pre fin, r = clauses_t pre fin /\ Forall pair_clause pre /\ (no_true_cl cs -> ce cl_err sc = LOk fin).
Proof.
 intros L sym ce n cs sc r HL H. rewrite admitted_patch_defs in H by exact HL.
 exact (patched_cond_final_t sym ce n cs sc r H).
Qed.
