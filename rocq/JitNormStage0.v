(* Shen/JIT Phase 2, pass split: translation validation of the EMIT pass alone, at stage 0.

   For each definition: the form as read (<file>.forms), lower.shen's normal form of its body
   (<file>.norm, a witness captured from `shen-jit.lower.norm Params (shen-jit.lower.share Body)`)
   and its code object (<file>.sbc), all decoded here from generic trees (JitLowerStage0.sx, from
   the trusted tokenizer tests/shen-jit/stage0_to_rocq.py, OB-JIT-LOWER-READER). The judge
   accepts when the names and parameters agree, the witness erases (JitNorm.erase), and the
   EXISTING checker JitLowerCheck.check_fn relates the code to the erasure.

   Acceptance therefore says: this code is a lowering, in JitLowerRel's sense, of erase(witness).
   It says NOTHING about whether the witness is the normal form of the source body, or equivalent
   to it: every accepted verdict carries `FrontEndUnchecked`, and that is wave 2's obligation
   (share and norm preserve meaning). Rejection proves nothing either way. *)
From Coq Require Import List ZArith NArith PArith Bool String Ascii.
From Buri Require Import Observation KLSyntax KLValue KLSemantics JitBytecode JitLowerRel JitLowerCheck JitLowerStage0 JitNorm.
Import ListNotations.
Module JitNormStage0.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel JitLowerCheck.JitLowerCheck.
Import JitLowerStage0.JitLowerStage0 JitNorm.JitNorm.
Module B := JitBytecode.JitBytecode.

(* ---------- decoding a witness ---------- *)
(* Node shapes as printed by stage0.shen's writer: (const V) (var X) (if C X Y) (and X Y)
   (or X Y) (let X V B) (do X Y) (lambda X B) (freeze B) (prim Op (A ...)) (call F (A ...))
   (apply F) (apply F X) (trap X E H). A constant decodes as data exactly as a form does
   (to_value: true/false are booleans, () is the empty list). Anything else: None. *)
Fixpoint decode (x : sx) : option nexpr :=
 match x with
 | XList (XSym h :: rest) =>
   let args := fix args (l : list sx) : option (list nexpr) := match l with
     | [] => Some []
     | a :: l => match decode a, args l with Some n, Some ns => Some (n :: ns) | _, _ => None end end in
   if String.eqb h "const" then match rest with [v] => Some (NConst (to_value v)) | _ => None end
   else if String.eqb h "var" then match rest with [XSym y] => Some (NVar (of_string y)) | _ => None end
   else if String.eqb h "if" then match rest with
     | [c; a; b] => match decode c, decode a, decode b with
       | Some c, Some a, Some b => Some (NIf c a b) | _, _, _ => None end
     | _ => None end
   else if String.eqb h "and" then match rest with
     | [a; b] => match decode a, decode b with Some a, Some b => Some (NAnd a b) | _, _ => None end
     | _ => None end
   else if String.eqb h "or" then match rest with
     | [a; b] => match decode a, decode b with Some a, Some b => Some (NOr a b) | _, _ => None end
     | _ => None end
   else if String.eqb h "let" then match rest with
     | [XSym y; v; b] => match decode v, decode b with
       | Some v, Some b => Some (NLet (of_string y) v b) | _, _ => None end
     | _ => None end
   else if String.eqb h "do" then match rest with
     | [a; b] => match decode a, decode b with Some a, Some b => Some (NDo a b) | _, _ => None end
     | _ => None end
   else if String.eqb h "lambda" then match rest with
     | [XSym y; b] => option_map (NLambda (of_string y)) (decode b)
     | _ => None end
   else if String.eqb h "freeze" then match rest with
     | [b] => option_map NFreeze (decode b)
     | _ => None end
   else if String.eqb h "prim" then match rest with
     | [XSym op; XList l] => option_map (NPrim (of_string op)) (args l)
     | _ => None end
   else if String.eqb h "call" then match rest with
     | [XSym f; XList l] => option_map (NCall (of_string f)) (args l)
     | _ => None end
   else if String.eqb h "apply" then match rest with
     | [f] => option_map NApply0 (decode f)
     | [f; a] => match decode f, decode a with Some f, Some a => Some (NApply1 f a) | _, _ => None end
     | _ => None end
   else if String.eqb h "trap" then match rest with
     | [b; XSym y; hd] => match decode b, decode hd with
       | Some b, Some hd => Some (NTrap b (of_string y) hd) | _, _ => None end
     | _ => None end
   else None
 | _ => None end.

Fixpoint syms (l : list sx) : option (list name) := match l with
 | [] => Some []
 | XSym s :: l => option_map (cons (of_string s)) (syms l)
 | _ => None end.

(* One witness entry: (F (P1 ... Pn) N). *)
Definition decode_entry (x : sx) : option (name * list name * nexpr) := match x with
 | XList [XSym f; XList ps; n] => match syms ps, decode n with
   | Some ps, Some n => Some (of_string f, ps, n) | _, _ => None end
 | _ => None end.

Fixpoint names_eqb (a b : list name) : bool := match a, b with
 | [], [] => true | x :: a, y :: b => text_eqb x y && names_eqb a b | _, _ => false end.
Lemma names_eqb_eq : forall a b, names_eqb a b = true -> a = b.
Proof.
 induction a as [|x a IH]; destruct b as [|y b]; cbn; intro H; try discriminate; auto.
 apply andb_true_iff in H as [H1 H2]. apply text_eqb_eq in H1. subst. f_equal. auto.
Qed.

(* ---------- the judge ---------- *)
(* The only front-end status this file can give. *)
Inductive front_end := FrontEndUnchecked.

(* The emit-pass verdict on one definition. *)
Inductive core :=
 | CAccepted (f : name) (ports : list name) (folds : nat)
 | CRejected (f : name)
 | CEraseFailed (f : name)
 | CUnparsed.

Definition judge_core (form norm sbc : sx) : core :=
 match parse [] (to_value form), to_val sbc with
 | Some (EDefun f ps b), B.VPair (B.VSym _) (B.VPair (B.VSym g) (B.VPair code B.VNil)) =>
   if negb (Pos.eqb (B.sym_of_text f) g) then CUnparsed else
   match decode_entry norm with
   | Some (f', ps', n) =>
     if negb (text_eqb f f' && names_eqb ps ps') then CUnparsed else
     match erase ps n with
     | None => CEraseFailed f
     | Some e =>
       match B.build_code B.prim_tree 64 code with
       | B.LOk c =>
         if (N.eqb (B.code_arity c) (N.of_nat (List.length ps))
             && match B.code_entry c with None => true | Some _ => false end
             && check_fn c ps e)%bool
         then CAccepted f (port_prims n) (folded n)
         else CRejected f
       | B.LErr _ => CRejected f end end
   | None => CUnparsed end
 | _, _ => CUnparsed end.

Inductive nverdict :=
 (* check_fn c ps (erase witness) holds. `ports`: port primitives the erasure calls, which have no
    KL meaning yet; `folds`: pair constants erased to cons chains; `src`: whether the stage 0
    judge (JitLowerStage0.judge, check_fn on the source body itself) accepts the definition. *)
 | NAccepted (f : name) (ports : list name) (folds : nat) (src : bool) (fe : front_end)
 | NRejected (f : name) (src : bool)   (* the witness erases, check_fn does not hold *)
 | NEraseFailed (f : name)             (* erase gave None *)
 | NUnparsed.                          (* a tree did not decode, or names/parameters disagree *)

Definition judge_norm (form norm sbc : sx) : nverdict :=
 let src := match judge form sbc with Accepted _ => true | _ => false end in
 match judge_core form norm sbc with
 | CAccepted f ports folds => NAccepted f ports folds src FrontEndUnchecked
 | CRejected f => NRejected f src
 | CEraseFailed f => NEraseFailed f
 | CUnparsed => NUnparsed end.

(* Close a branch whose verdict is not CAccepted, reducing only what the branch fixed: a
   general `discriminate` would unfold check_fn's fuel. *)
Ltac bad H := cbn [negb andb] in H; cbv beta iota zeta in H;
 match type of H with
 | CUnparsed = _ => discriminate H | CRejected _ = _ => discriminate H
 | CEraseFailed _ = _ => discriminate H end.

Lemma judge_core_sound : forall form norm sbc f ports folds,
 judge_core form norm sbc = CAccepted f ports folds ->
 exists ps b n e code c h,
   parse [] (to_value form) = Some (EDefun f ps b) /\
   to_val sbc = B.VPair (B.VSym h) (B.VPair (B.VSym (B.sym_of_text f)) (B.VPair code B.VNil)) /\
   decode_entry norm = Some (f, ps, n) /\
   erase ps n = Some e /\
   B.build_code B.prim_tree 64 code = B.LOk c /\
   B.code_arity c = N.of_nat (List.length ps) /\ B.code_entry c = None /\
   CompFn c ps e.
Proof.
 intros form norm sbc f ports folds H. unfold judge_core in H.
 destruct (parse [] (to_value form)) as [ex|] eqn:Pf; [|bad H].
 destruct ex as [  |  |  |  |  |  |  |  |  |  |  |  |  |  |  | f0 ps b |  |  ]; try bad H.
 destruct (to_val sbc) as [  |  |  |  |  |  |  | x1 y1 |  |  |  |  |  |  ] eqn:Ts; try bad H.
 destruct x1 as [  |  | h |  |  |  |  |  |  |  |  |  |  |  ]; try bad H.
 destruct y1 as [  |  |  |  |  |  |  | x2 y2 |  |  |  |  |  |  ]; try bad H.
 destruct x2 as [  |  | g |  |  |  |  |  |  |  |  |  |  |  ]; try bad H.
 destruct y2 as [  |  |  |  |  |  |  | code y3 |  |  |  |  |  |  ]; try bad H.
 destruct y3; try bad H.
 destruct (Pos.eqb (B.sym_of_text f0) g) eqn:Eg; [|bad H].
 apply Pos.eqb_eq in Eg; subst g.
 destruct (decode_entry norm) as [[[f' ps'] n]|] eqn:De; [|bad H].
 destruct (text_eqb f0 f' && names_eqb ps ps')%bool eqn:En; [|bad H].
 apply andb_true_iff in En as [E1 E2]. apply text_eqb_eq in E1. apply names_eqb_eq in E2. subst f' ps'.
 destruct (erase ps n) as [e|] eqn:Er; [|bad H].
 destruct (B.build_code B.prim_tree 64 code) as [c|] eqn:Bc; [|bad H].
 destruct (N.eqb (B.code_arity c) (N.of_nat (List.length ps))) eqn:Ar; [|bad H].
 destruct (B.code_entry c) eqn:En; [bad H|].
 destruct (check_fn c ps e) eqn:Ck; [|bad H].
 cbn [negb andb] in H. cbv beta iota in H.
 injection H as Hf _ _. subst f0. apply N.eqb_eq in Ar.
 exists ps, b, n, e, code, c, h.
 refine (conj eq_refl (conj eq_refl (conj eq_refl (conj Er (conj Bc (conj Ar (conj En _))))))).
 apply check_fn_sound; exact Ck.
Qed.

(* What acceptance proves: the definition parses, the witness decodes with the same name and
   parameters, it erases to e, and the code object is a lowering of e (CompFn), with the stage 0
   shape. Not that e has anything to do with the definition's body b. *)
Theorem judge_norm_sound : forall form norm sbc f ports folds src fe,
 judge_norm form norm sbc = NAccepted f ports folds src fe ->
 exists ps b n e code c h,
   parse [] (to_value form) = Some (EDefun f ps b) /\
   to_val sbc = B.VPair (B.VSym h) (B.VPair (B.VSym (B.sym_of_text f)) (B.VPair code B.VNil)) /\
   decode_entry norm = Some (f, ps, n) /\
   erase ps n = Some e /\
   B.build_code B.prim_tree 64 code = B.LOk c /\
   B.code_arity c = N.of_nat (List.length ps) /\ B.code_entry c = None /\
   CompFn c ps e.
Proof.
 intros form norm sbc f ports folds src fe H. unfold judge_norm in H. cbv zeta in H.
 destruct (judge_core form norm sbc) as [f0 p0 fo0| | |] eqn:J; try discriminate H.
 apply (f_equal (fun v => match v with NAccepted f _ _ _ _ => f | _ => f0 end)) in H.
 cbv beta iota in H. subst f0. eapply judge_core_sound; exact J.
Qed.

(* ---------- per file ---------- *)
Fixpoint judge_norm_all (fs ns ss : list sx) : list nverdict := match fs, ns, ss with
 | f :: fs, n :: ns, s :: ss => judge_norm f n s :: judge_norm_all fs ns ss
 | [], [], [] => []
 | _, _, _ => [NUnparsed] end.

(* Names, printable (code points below 256 only; the stage 0 files are ASCII). *)
Definition show (t : name) : string :=
 fold_right (fun c s => String (ascii_of_N c) s) EmptyString t.
Fixpoint add_new (x : string) (l : list string) : list string := match l with
 | [] => [x] | y :: l => if String.eqb x y then y :: l else y :: add_new x l end.

Record ntally := NTally {
 accepted : nat;          (* check_fn on the erased witness *)
 rejected : nat;
 erase_failed : nat;
 unparsed : nat;
 front_end_unchecked : nat; (* = accepted: no acceptance here says anything about the front end *)
 with_port_prims : nat;   (* accepted, but the erasure calls a port primitive with no KL meaning *)
 with_folds : nat;        (* accepted, and the erasure has a cons chain for a folded constant *)
 src_accepted : nat;      (* the stage 0 judge's verdict on the source body, for comparison *)
 lost : list string;      (* accepted on the source body, not on the witness *)
 gained : list string;    (* accepted on the witness, not on the source body *)
 port_prims_used : list string }.

Definition tally_step (v : nverdict) (t : ntally) : ntally :=
 let '(NTally a r x u fe wp wf sa lo ga pu) := t in
 match v with
 | NAccepted f ports folds src _ =>
   NTally (S a) r x u (S fe) (match ports with [] => wp | _ => S wp end)
          (match folds with O => wf | _ => S wf end) (if src then S sa else sa)
          lo (if src then ga else show f :: ga) (fold_right add_new pu (map show ports))
 | NRejected f src => NTally a (S r) x u fe wp wf (if src then S sa else sa)
          (if src then show f :: lo else lo) ga pu
 | NEraseFailed _ => NTally a r (S x) u fe wp wf sa lo ga pu
 | NUnparsed => NTally a r x (S u) fe wp wf sa lo ga pu end.

Definition tally_norm (fs ns ss : list sx) : ntally :=
 fold_right tally_step (NTally 0 0 0 0 0 0 0 0 [] [] []) (judge_norm_all fs ns ss).
End JitNormStage0.
