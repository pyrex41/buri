(* E2E-22 (chezprim lane): translation validation of the primitive-expansion
   step for a two-argument `+` call ($np-expand-primitives, cpprim.ss
   build-fxop?, L7 -> L9), with a stated word-level semantics.

   The semantics covers exactly the constructs this expansion produces and
   consumes, read from the raw (info-carrying) dump:
     uvar references and (immediate n) trivials;
     (inline #[info:info] %logor t1 t2), (inline #[info:info] %+/ovfl t1 t2);
     (if P e1 e2) with P one of
       (inline #[info:info] %log!test e t)                -- (e & t) = 0
       (inline #[info:info-condition-code type= overflow reversed?= #f
                 invertible?= #t] %condition-code)          -- last overflow flag;
     (let ([x e]) body), (label L e), (goto L), (seq (pariah) e);
     (call INFO #f PRIMREF t ...)                           -- the primitive itself;
     (call INFO #f (literal #[info:info-literal indirect?= #f type= library
                  addr= #(libspec NAME n) offset= 0]) t ...) -- library entry NAME.
   Anything else is rejected.

   Semantic choices, stated so no claim outgrows them:
   * Values are 64-bit machine words (integers in [0, 2^64), ChezWord).
   * Operands of inline operations and calls are trivials (variables,
     immediates), so evaluation order cannot matter and none is chosen.
   * %+/ovfl yields wrap (a + b) and sets the overflow flag iff the signed
     sum leaves [-2^63, 2^63); %condition-code reads that flag.  Every other
     operation clobbers the flag (it becomes unknown and a later
     %condition-code is stuck), which is stricter than the hardware.
   * %log!test is true iff (e & t) = 0 (arm64.ss asm-logtest with i? = #t:
     tst, then branch on eq to the true label).
   * label/goto: labels are function-scoped (Chez local-labels); goto L
     evaluates L's body in the current environment.
   * (pariah), and the info-call fields pariah?/error?/src/sexpr, are
     placement hints and source data with no effect on the value.
   * The primitive and the library entries are arbitrary parameters over an
     arbitrary world.  The soundness theorem assumes, as premises:
     (H_fix) Scheme `+` on two fixnums whose sum is a fixnum returns the
             fixnum of the sum and leaves the world unchanged;
     (H_lib) the library entry `+` behaves as the primitive `+` on every
             argument list (obligation OB-CHEZ-LIB-PLUS; nothing here checks
             the library code).
   Nothing here is about register allocation, instruction selection or the
   bytes; see docs/CHEZ-NANOPASS.md section 9 for what connects. *)
From Coq Require Import String List Bool Arith ZArith Lia.
From Buri Require Import ChezLayout ChezWord ChezNpReader ChezNpCore ChezPrimRaw.
Import ListNotations.
Open Scope string_scope.
Import ChezWord.ChezWord.

Inductive triv : Type :=
| TVar : string -> triv
| TImm : Z -> triv.

Inductive wexpr : Type :=
| WTriv : triv -> wexpr
| WLogor : triv -> triv -> wexpr
| WAddOvfl : triv -> triv -> wexpr
| WIf : wpred -> wexpr -> wexpr -> wexpr
| WLet : string -> wexpr -> wexpr -> wexpr
| WLabel : string -> wexpr -> wexpr
| WGoto : string -> wexpr
| WPariah : wexpr -> wexpr
| WCallPrim : string -> list triv -> wexpr
| WCallLib : string -> list triv -> wexpr
with wpred : Type :=
| PLogNotTest : wexpr -> triv -> wpred
| POverflow : wpred.

(* ---- reading raw L7 / L9 ------------------------------------------------ *)

Definition z_of_atom (x : sexp) : option Z :=
  match x with
  | Atom a =>
      match a with
      | String c r =>
          if is c 45 then option_map (fun n => Z.opp (Z.of_nat n)) (nat_of_atom (Atom r))
          else option_map Z.of_nat (nat_of_atom x)
      | EmptyString => None
      end
  | _ => None
  end.

Definition read_triv (x : sexp) : option triv :=
  match x with
  | Atom _ => option_map TVar (is_uvar_atom x)
  | Lst [Atom kw; n] => if String.eqb kw "immediate" then option_map TImm (z_of_atom n) else None
  | _ => None
  end.

Fixpoint read_trivs (xs : list sexp) : option (list triv) :=
  match xs with
  | [] => Some []
  | x :: r =>
      match read_triv x, read_trivs r with
      | Some t, Some ts => Some (t :: ts)
      | _, _ => None
      end
  end.

Definition is_null_info (x : sexp) : bool :=
  match x with Rec [Atom a] => String.eqb a "info:info" | _ => false end.

Definition is_overflow_cc_info (x : sexp) : bool :=
  match x with
  | Rec [Atom a; Atom k1; Atom v1; Atom k2; Atom v2; Atom k3; Atom v3] =>
      String.eqb a "info:info-condition-code" &&
      String.eqb k1 "type=" && String.eqb v1 "overflow" &&
      String.eqb k2 "reversed?=" && String.eqb v2 "#f" &&
      String.eqb k3 "invertible?=" && String.eqb v3 "#t"
  | _ => false
  end.

(* A call's info record: the ChezPrimRaw acceptance condition, with a
   primref or library-entry operator (both procedures). *)
Definition wcall_info_ok (info : sexp) : bool := ChezPrimRaw.call_info_ok info true.

(* (literal #[info:info-literal indirect?= #f type= library
              addr= #(libspec NAME n) offset= 0]) names library entry NAME. *)
Definition library_literal (x : sexp) : option string :=
  match x with
  | Lst [Atom kw; Rec [Atom a; Atom k1; Atom v1; Atom k2; Atom v2; Atom k3;
                       Vec [Atom ls; Atom nm; _]; Atom k4; Atom v4]] =>
      if String.eqb kw "literal" && String.eqb a "info:info-literal" &&
         String.eqb k1 "indirect?=" && String.eqb v1 "#f" &&
         String.eqb k2 "type=" && String.eqb v2 "library" &&
         String.eqb k3 "addr=" && String.eqb ls "libspec" &&
         String.eqb k4 "offset=" && String.eqb v4 "0"
      then Some nm else None
  | _ => None
  end.

(* A primref record #[primref.UID NAME FLAGS ARITY] names primitive NAME. *)
Definition primref_name (x : sexp) : option string :=
  match x with
  | Rec (Atom a :: Atom nm :: _) => if prefix "primref." a then Some nm else None
  | _ => None
  end.

Fixpoint wden (fuel : nat) (x : sexp) : option wexpr :=
  match fuel with
  | O => None
  | S f =>
      let pred (p : sexp) : option wpred :=
        match p with
        | Lst [Atom kw; info; Atom op; e; t] =>
            if String.eqb kw "inline" && is_null_info info && String.eqb op "%log!test" then
              match wden f e, read_triv t with
              | Some e', Some t' => Some (PLogNotTest e' t')
              | _, _ => None
              end
            else None
        | Lst [Atom kw; info; Atom op] =>
            if String.eqb kw "inline" && is_overflow_cc_info info && String.eqb op "%condition-code"
            then Some POverflow else None
        | _ => None
        end in
      match x with
      | Atom _ => option_map WTriv (read_triv x)
      | Lst (Atom kw :: rest) =>
          if String.eqb kw "immediate" then option_map WTriv (read_triv x)
          else if String.eqb kw "inline" then
            match rest with
            | [info; Atom op; a; b] =>
                if is_null_info info then
                  match read_triv a, read_triv b with
                  | Some a', Some b' =>
                      if String.eqb op "%logor" then Some (WLogor a' b')
                      else if String.eqb op "%+/ovfl" then Some (WAddOvfl a' b')
                      else None
                  | _, _ => None
                  end
                else None
            | _ => None
            end
          else if String.eqb kw "goto" then
            match rest with [Atom l] => Some (WGoto l) | _ => None end
          else if String.eqb kw "if" then
            match rest with
            | [p; a; b] =>
                match pred p, wden f a, wden f b with
                | Some p', Some a', Some b' => Some (WIf p' a' b')
                | _, _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "let" then
            match rest with
            | [Lst [Lst [v; e]]; body] =>
                match is_uvar_atom v, wden f e, wden f body with
                | Some v', Some e', Some b' => Some (WLet v' e' b')
                | _, _, _ => None
                end
            | _ => None
            end
          else if String.eqb kw "label" then
            match rest with [Atom l; body] => option_map (WLabel l) (wden f body) | _ => None end
          else if String.eqb kw "seq" then
            match rest with
            | [Lst [Atom p]; e] => if String.eqb p "pariah" then option_map WPariah (wden f e) else None
            | _ => None
            end
          else if String.eqb kw "call" then
            match rest with
            | info :: Atom mdcl :: op :: args =>
                if String.eqb mdcl "#f" && wcall_info_ok info then
                  match read_trivs args with
                  | Some ts =>
                      match primref_name op, library_literal op with
                      | Some nm, _ => Some (WCallPrim nm ts)
                      | None, Some nm => Some (WCallLib nm ts)
                      | None, None => None
                      end
                  | None => None
                  end
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  end.

Definition wden_fuel : nat := 64.

(* ---- semantics ---------------------------------------------------------- *)

Fixpoint wlabels (e : wexpr) : list (string * wexpr) :=
  match e with
  | WIf p a b => app (plabels p) (app (wlabels a) (wlabels b))
  | WLet _ a b => app (wlabels a) (wlabels b)
  | WLabel l b => (l, b) :: wlabels b
  | WPariah b => wlabels b
  | _ => []
  end
with plabels (p : wpred) : list (string * wexpr) :=
  match p with
  | PLogNotTest e _ => wlabels e
  | POverflow => []
  end.

Definition signed_overflow (a b : Z) : bool :=
  negb (Z.leb (- half) (swrap a + swrap b) && Z.ltb (swrap a + swrap b) half).

Section Sem.
  Variable World : Type.
  (* the primitive NAME and the library entry NAME, on machine words *)
  Variable prim : string -> list Z -> World -> option (Z * World).
  Variable lib : string -> list Z -> World -> option (Z * World).

  Fixpoint wlookup (x : string) (env : list (string * Z)) : option Z :=
    match env with
    | [] => None
    | (y, v) :: r => if String.eqb x y then Some v else wlookup x r
    end.

  Definition tval (env : list (string * Z)) (t : triv) : option Z :=
    match t with TVar x => wlookup x env | TImm z => Some z end.

  Fixpoint tvals (env : list (string * Z)) (ts : list triv) : option (list Z) :=
    match ts with
    | [] => Some []
    | t :: r =>
        match tval env t, tvals env r with
        | Some v, Some vs => Some (v :: vs)
        | _, _ => None
        end
    end.

  Fixpoint label_body (l : string) (lt : list (string * wexpr)) : option wexpr :=
    match lt with
    | [] => None
    | (l', b) :: r => if String.eqb l l' then Some b else label_body l r
    end.

  (* Result: the word, the overflow flag (None = unknown), the world. *)
  Fixpoint weval (fuel : nat) (lt : list (string * wexpr)) (env : list (string * Z))
      (fl : option bool) (e : wexpr) (w : World) {struct fuel} : option (Z * option bool * World) :=
    match fuel with
    | O => None
    | S f =>
        match e with
        | WTriv t => option_map (fun v => (v, fl, w)) (tval env t)
        | WLogor a b =>
            match tval env a, tval env b with
            | Some x, Some y => Some (Z.lor x y, None, w)
            | _, _ => None
            end
        | WAddOvfl a b =>
            match tval env a, tval env b with
            | Some x, Some y => Some (wrap (x + y), Some (signed_overflow x y), w)
            | _, _ => None
            end
        | WIf p a b =>
            match wpeval f lt env fl p w with
            | Some (true, fl', w') => weval f lt env fl' a w'
            | Some (false, fl', w') => weval f lt env fl' b w'
            | None => None
            end
        | WLet x a b =>
            match weval f lt env fl a w with
            | Some (v, fl', w') => weval f lt ((x, v) :: env) fl' b w'
            | None => None
            end
        | WLabel _ b => weval f lt env fl b w
        | WGoto l => match label_body l lt with Some b => weval f lt env fl b w | None => None end
        | WPariah b => weval f lt env fl b w
        | WCallPrim nm ts =>
            match tvals env ts with
            | Some vs => option_map (fun r => (fst r, None, snd r)) (prim nm vs w)
            | None => None
            end
        | WCallLib nm ts =>
            match tvals env ts with
            | Some vs => option_map (fun r => (fst r, None, snd r)) (lib nm vs w)
            | None => None
            end
        end
    end
  with wpeval (fuel : nat) (lt : list (string * wexpr)) (env : list (string * Z))
      (fl : option bool) (p : wpred) (w : World) {struct fuel} : option (bool * option bool * World) :=
    match fuel with
    | O => None
    | S f =>
        match p with
        | PLogNotTest e t =>
            match weval f lt env fl e w, tval env t with
            | Some (v, _, w'), Some m => Some (Z.eqb (Z.land v m) 0, None, w')
            | _, _ => None
            end
        | POverflow => match fl with Some b => Some (b, fl, w) | None => None end
        end
    end.

  (* The value of a clause body in an environment of formals: labels are
     collected from the body, the flag starts unknown. *)
  Definition run (fuel : nat) (env : list (string * Z)) (e : wexpr) (w : World) : option (Z * World) :=
    option_map (fun r => let '(v, _, w') := r in (v, w')) (weval fuel (wlabels e) env None e w).
End Sem.

(* ---- the validator ------------------------------------------------------ *)

Definition triv_var (t : triv) : option string := match t with TVar x => Some x | TImm _ => None end.

Definition is_var (x : string) (t : triv) : bool :=
  match t with TVar y => String.eqb x y | TImm _ => false end.

(* The exact cpprim.ss build-fxop? shape for `+` on a and b:
     (if (log!test (logor a b) 7)
         (let ([t (+/ovfl a b)])
           (if (condition-code overflow) (label L (pariah; (lib + a b))) t))
         (goto L))
   with t different from a and b (it must not shadow them). *)
Definition plus_expansion (a b : string) (o : wexpr) : bool :=
  match o with
  | WIf (PLogNotTest (WLogor a1 b1) (TImm m))
        (WLet t (WAddOvfl a2 b2)
           (WIf POverflow (WLabel l (WPariah (WCallLib nm [a3; b3]))) (WTriv t1)))
        (WGoto l1) =>
      is_var a a1 && is_var b b1 && Z.eqb m 7 &&
      is_var a a2 && is_var b b2 && is_var a a3 && is_var b b3 &&
      String.eqb nm "+" && is_var t t1 && String.eqb l l1 &&
      negb (String.eqb t a) && negb (String.eqb t b)
  | _ => false
  end.

Definition check_expand_plus (input output : wexpr) : bool :=
  match input with
  | WCallPrim nm [TVar a; TVar b] => String.eqb nm "+" && plus_expansion a b output
  | _ => false
  end.

(* ---- soundness ---------------------------------------------------------- *)

Definition fix_plus_contract {World} (prim : string -> list Z -> World -> option (Z * World)) : Prop :=
  forall x y w, fx_range x -> fx_range y -> fx_range (x + y) ->
    prim "+" [fx_enc x; fx_enc y] w = Some (fx_enc (x + y), w).

Definition lib_plus_is_prim {World} (prim lib : string -> list Z -> World -> option (Z * World)) : Prop :=
  forall vs w, lib "+" vs w = prim "+" vs w.

Lemma mask7 : ChezLayout.ChezLayout.mask_fixnum = 7%Z.
Proof. destruct chez_word_layout as (_ & _ & _ & HK & _). exact HK. Qed.

Lemma is_var_eq : forall x t, is_var x t = true -> t = TVar x.
Proof.
  intros x [y|z] H; simpl in H; [apply String.eqb_eq in H; subst; reflexivity | discriminate].
Qed.

Lemma plus_expansion_shape : forall a b o, plus_expansion a b o = true ->
  exists t l, o = WIf (PLogNotTest (WLogor (TVar a) (TVar b)) (TImm 7))
        (WLet t (WAddOvfl (TVar a) (TVar b))
           (WIf POverflow (WLabel l (WPariah (WCallLib "+" [TVar a; TVar b]))) (WTriv (TVar t))))
        (WGoto l) /\ t <> a /\ t <> b.
Proof.
  intros a b o H.
  unfold plus_expansion in H.
  repeat match type of H with
  | context [match ?x with _ => _ end] => destruct x; try discriminate H
  end.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[[[[[[[[[[Ha1 Hb1] Hm] Ha2] Hb2] Ha3] Hb3] Hnm] Ht1] Hl] Hta] Htb].
  apply is_var_eq in Ha1, Hb1, Ha2, Hb2, Ha3, Hb3, Ht1. subst.
  apply Z.eqb_eq in Hm. apply String.eqb_eq in Hnm. apply String.eqb_eq in Hl. subst.
  do 2 eexists. split; [reflexivity|].
  apply Bool.negb_true_iff, String.eqb_neq in Hta.
  apply Bool.negb_true_iff, String.eqb_neq in Htb.
  split; assumption.
Qed.

Lemma lookup_shadow : forall t a (v : Z) env, t <> a -> wlookup a ((t, v) :: env) = wlookup a env.
Proof.
  intros t a v env H. simpl.
  destruct (String.eqb a t) eqn:E; [apply String.eqb_eq in E; congruence | reflexivity].
Qed.

(* The fast path, without any premise on the primitive or the library: when
   a and b hold fixnum words of x and y and x + y is a fixnum, the expansion
   returns the fixnum word of x + y and calls nothing. *)
Theorem plus_expansion_fast :
  forall a b o, plus_expansion a b o = true ->
  forall World prim lib (env : list (string * Z)) x y (w : World) (fuel : nat),
    wlookup a env = Some (fx_enc x) -> wlookup b env = Some (fx_enc y) ->
    fx_range x -> fx_range y -> fx_range (x + y) -> (6 <= fuel)%nat ->
    run World prim lib fuel env o w = Some (fx_enc (x + y), w).
Proof.
  intros a b o H World prim lib env x y w fuel Ha Hb Hx Hy Hxy Hf.
  destruct (plus_expansion_shape a b o H) as (t & l & -> & Hta & Htb).
  do 6 (destruct fuel as [|fuel]; [lia|]).
  unfold run. simpl. rewrite Ha, Hb.
  pose proof (fx_or_tag x y) as T. rewrite mask7 in T. rewrite T. simpl.
  rewrite ?Ha, ?Hb.
  assert (Hno : signed_overflow (fx_enc x) (fx_enc y) = false).
  { unfold signed_overflow. apply (fx_add_no_overflow_iff x y Hx Hy) in Hxy.
    apply Bool.negb_false_iff. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hno. simpl. rewrite String.eqb_refl. simpl. rewrite fx_add_wrap. reflexivity.
Qed.

(* The slow path: when the tag test or the overflow test fails, the
   expansion's value is the library entry `+` on a and b. *)
Theorem plus_expansion_slow :
  forall a b o, plus_expansion a b o = true ->
  forall World prim lib (env : list (string * Z)) va vb (w : World) (fuel : nat),
    wlookup a env = Some va -> wlookup b env = Some vb -> (6 <= fuel)%nat ->
    (Z.land (Z.lor va vb) 7 <> 0 \/ signed_overflow va vb = true) ->
    run World prim lib fuel env o w = lib "+" [va; vb] w.
Proof.
  intros a b o H World prim lib env va vb w fuel Ha Hb Hf Hslow.
  destruct (plus_expansion_shape a b o H) as (t & l & -> & Hta & Htb).
  do 6 (destruct fuel as [|fuel]; [lia|]).
  unfold run. simpl. rewrite Ha, Hb.
  destruct (Z.eqb (Z.land (Z.lor va vb) 7) 0) eqn:T.
  - apply Z.eqb_eq in T. destruct Hslow as [Hs|Hs]; [contradiction|].
    assert (Eat : String.eqb a t = false) by (apply String.eqb_neq; congruence).
    assert (Ebt : String.eqb b t = false) by (apply String.eqb_neq; congruence).
    simpl. rewrite ?Ha, ?Hb. rewrite Hs, Eat, Ebt. simpl.
    destruct (lib "+" [va; vb] w) as [[r w']|]; reflexivity.
  - simpl. rewrite String.eqb_refl. simpl. rewrite Ha, Hb.
    destruct (lib "+" [va; vb] w) as [[r w']|]; reflexivity.
Qed.

(* Universal theorem: every pair the validator accepts has the same value
   and final world, in every environment of machine words, for every
   primitive and library semantics satisfying H_fix and H_lib (fuel >= 6
   suffices for the expansion; the input needs 1). *)
Theorem check_expand_plus_sound :
  forall input output, check_expand_plus input output = true ->
  forall World prim lib, fix_plus_contract (World := World) prim -> lib_plus_is_prim prim lib ->
  forall (env : list (string * Z)) (w : World) (fuel : nat),
    (forall v z, wlookup v env = Some z -> word_ok z) -> (6 <= fuel)%nat ->
    run World prim lib fuel env output w = run World prim lib fuel env input w.
Proof.
  intros input output H World prim lib Hfix Hlib env w fuel Henv Hf.
  destruct input as [| | | | | | | | nm ts |]; try discriminate H.
  destruct ts as [|[a|] [|[b|] [|]]]; try discriminate H.
  simpl in H. apply Bool.andb_true_iff in H. destruct H as [Hnm H].
  apply String.eqb_eq in Hnm. subst nm.
  assert (Hin : forall va vb, wlookup a env = Some va -> wlookup b env = Some vb ->
            run World prim lib fuel env (WCallPrim "+" [TVar a; TVar b]) w = prim "+" [va; vb] w).
  { intros va vb Ha Hb. destruct fuel as [|fuel]; [lia|].
    unfold run. simpl. rewrite Ha, Hb. destruct (prim "+" [va; vb] w) as [[r w']|]; reflexivity. }
  destruct (wlookup a env) as [va|] eqn:Ha.
  2: { destruct (plus_expansion_shape a b output H) as (t & l & -> & _ & _).
       do 6 (destruct fuel as [|fuel]; [lia|]). unfold run. simpl. rewrite Ha. reflexivity. }
  destruct (wlookup b env) as [vb|] eqn:Hb.
  2: { destruct (plus_expansion_shape a b output H) as (t & l & -> & _ & _).
       do 6 (destruct fuel as [|fuel]; [lia|]). unfold run. simpl. rewrite Ha, Hb. reflexivity. }
  rewrite (Hin va vb eq_refl eq_refl).
  destruct (Z.eqb (Z.land (Z.lor va vb) 7) 0) eqn:T.
  - apply Z.eqb_eq in T.
    rewrite <- mask7 in T. apply tag_or_iff in T. destruct T as [Ta Tb].
    destruct (fx_enc_dec va (Henv a va Ha) Ta) as [Rx Ex].
    destruct (fx_enc_dec vb (Henv b vb Hb) Tb) as [Ry Ey].
    set (x := fx_dec va) in *. set (y := fx_dec vb) in *.
    destruct (signed_overflow va vb) eqn:O.
    + rewrite (plus_expansion_slow a b output H World prim lib env va vb w fuel Ha Hb Hf (or_intror O)).
      apply Hlib.
    + assert (Hxy : fx_range (x + y)).
      { apply (fx_add_no_overflow_iff x y Rx Ry). rewrite Ex, Ey.
        unfold signed_overflow in O. apply Bool.negb_false_iff, Bool.andb_true_iff in O.
        destruct O as [O1 O2]. apply Z.leb_le in O1. apply Z.ltb_lt in O2. lia. }
      rewrite <- Ex in Ha. rewrite <- Ey in Hb.
      rewrite (plus_expansion_fast a b output H World prim lib env x y w fuel Ha Hb Rx Ry Hxy Hf).
      rewrite <- Ex, <- Ey. symmetry. apply Hfix; assumption.
  - rewrite (plus_expansion_slow a b output H World prim lib env va vb w fuel Ha Hb Hf).
    + apply Hlib.
    + left. intro E. apply Z.eqb_neq in T. contradiction.
Qed.
