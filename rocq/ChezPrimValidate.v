(* E2E-22 (chezprim lane): ground derivations on the raw capture of
     (define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))
   (ports/chez-np/tarm64le-buri-arm-add.raw.np).

   Each theorem applies a universal checker theorem (ChezPrimExpand,
   ChezPrimBlocks) to this one artifact.  None is a theorem about Chez on
   other programs, and none is about the dumping tool's faithfulness
   (OB-CHEZ-NP-RAW-DUMP). *)
From Coq Require Import String List Bool ZArith.
From Buri Require Import ChezLayout ChezWord ChezNpReader ChezNpCore ChezPrimRawInput ChezPrimRaw
  ChezPrimExpand ChezPrimBlocks.
Import ListNotations.
Open Scope string_scope.
Import ChezWord.ChezWord.

(* ---- $np-expand-primitives on kl:buri-arm-add (L7 -> L9) ---------------- *)

(* (labels ((NAME (case-lambda INFO [clause (x ...) mcp n body])) ...) entry)
   gives (INFO, formals, mcp, n, body) of NAME's only clause. *)
Fixpoint find_binding (name : string) (bs : list sexp) : option sexp :=
  match bs with
  | Lst [Atom n; e] :: r => if String.eqb n name then Some e else find_binding name r
  | _ :: r => find_binding name r
  | [] => None
  end.

Definition clause_parts (name : string) (o : option sexp) : option (sexp * sexp * sexp * sexp * sexp) :=
  match option_map expand_graph o with
  | Some (Some (Lst [Atom kw; Lst bs; _])) =>
      if String.eqb kw "labels" then
        match find_binding name bs with
        | Some (Lst [Atom cl; info; Lst [Atom c; formals; mcp; n; body]]) =>
            if String.eqb cl "case-lambda" && String.eqb c "clause"
            then Some (info, formals, mcp, n, body) else None
        | _ => None
        end
      else None
  | _ => None
  end.

Definition fname : string := "kl:buri-arm-add.17".

Definition expand_in_parts := clause_parts fname (raw_datum "np-unbox-fp-vars!").
Definition expand_out_parts := clause_parts fname (raw_datum "$np-expand-primitives").

Definition frame_of (o : option (sexp * sexp * sexp * sexp * sexp)) : option (sexp * sexp * sexp * sexp) :=
  option_map (fun p => let '(i, f, m, n, _) := p in (i, f, m, n)) o.

Definition body_w (o : option (sexp * sexp * sexp * sexp * sexp)) : wexpr :=
  match o with
  | Some (_, _, _, _, b) => match wden wden_fuel b with Some e => e | None => WGoto "" end
  | None => WGoto ""
  end.

Definition expand_in : wexpr := body_w expand_in_parts.
Definition expand_out : wexpr := body_w expand_out_parts.

(* Ground derivation: the pass kept the clause frame (info-lambda record,
   formals, mcp, interface) and the input body is the primitive `+` applied
   to the two formals, in order. *)
Theorem expand_frame_kept :
  frame_of expand_in_parts = frame_of expand_out_parts /\
  option_map (fun p => let '(_, f, _, n, _) := p in (f, n)) expand_in_parts =
    Some (Lst [Atom "V3015.12"; Atom "V3016.13"], Atom "2").
Proof. vm_compute. split; reflexivity. Qed.

Theorem expand_in_is_plus :
  expand_in = WCallPrim "+" [TVar "V3015.12"; TVar "V3016.13"].
Proof. vm_compute. reflexivity. Qed.

(* Ground derivation: the expanded body is exactly the build-fxop? shape. *)
Theorem expand_out_shape :
  expand_out =
  WIf (PLogNotTest (WLogor (TVar "V3015.12") (TVar "V3016.13")) (TImm 7))
    (WLet "t.19" (WAddOvfl (TVar "V3015.12") (TVar "V3016.13"))
       (WIf POverflow
          (WLabel "Lfail.20" (WPariah (WCallLib "+" [TVar "V3015.12"; TVar "V3016.13"])))
          (WTriv (TVar "t.19"))))
    (WGoto "Lfail.20").
Proof. vm_compute. reflexivity. Qed.

Theorem expand_plus_buri_arm_add_checked : check_expand_plus expand_in expand_out = true.
Proof. vm_compute. reflexivity. Qed.

(* Ground derivation from check_expand_plus_sound: for every primitive and
   library semantics meeting H_fix and H_lib and all argument words, the
   expanded body of kl:buri-arm-add has the value and final world of the
   primitive call it replaced. *)
Theorem expand_plus_buri_arm_add_preserves :
  forall World prim lib, fix_plus_contract (World := World) prim -> lib_plus_is_prim prim lib ->
  forall va vb (w : World) (fuel : nat), word_ok va -> word_ok vb -> (6 <= fuel)%nat ->
    run World prim lib fuel [("V3015.12", va); ("V3016.13", vb)] expand_out w =
    run World prim lib fuel [("V3015.12", va); ("V3016.13", vb)] expand_in w.
Proof.
  intros World prim lib Hfix Hlib va vb w fuel Ha Hb Hf.
  apply (check_expand_plus_sound _ _ expand_plus_buri_arm_add_checked World prim lib Hfix Hlib); auto.
  intros v z E. simpl in E.
  destruct (String.eqb v "V3015.12"); [injection E as <-; exact Ha|].
  destruct (String.eqb v "V3016.13"); [injection E as <-; exact Hb|discriminate].
Qed.

Lemma plus_out_ok : plus_expansion "V3015.12" "V3016.13" expand_out = true.
Proof. vm_compute. reflexivity. Qed.

(* The fast path at the Shen level, with no premise on the primitive or the
   library: if V3015 and V3016 hold the fixnum words of Shen integers x and
   y, and x, y and x + y are fixnums, the expanded body's value is
   fx_enc (x + y), the same ChezWord.fx_enc whose bit-vector image
   ports/arm/islaris/buri_chez_add_shen.v proves in X23 at the return
   address. *)
Theorem expanded_fast_path_shen :
  forall World prim lib x y (w : World) (fuel : nat),
    fx_range x -> fx_range y -> fx_range (x + y) -> (6 <= fuel)%nat ->
    run World prim lib fuel [("V3015.12", fx_enc x); ("V3016.13", fx_enc y)] expand_out w =
    Some (fx_enc (x + y), w).
Proof.
  intros. apply (plus_expansion_fast _ _ _ plus_out_ok); auto.
Qed.

Theorem expanded_slow_path :
  forall World prim lib va vb (w : World) (fuel : nat), (6 <= fuel)%nat ->
    (Z.land (Z.lor va vb) 7 <> 0 \/ signed_overflow va vb = true) ->
    run World prim lib fuel [("V3015.12", va); ("V3016.13", vb)] expand_out w = lib "+" [va; vb] w.
Proof.
  intros. apply (plus_expansion_slow _ _ _ plus_out_ok); auto.
Qed.

(* The validator is not vacuous: it rejects the next pass's output (whose
   trap-check form it does not read), and the expansion with the tag mask,
   the overflow-path entry or the operand order changed. *)
Definition expand_next : wexpr := body_w (clause_parts fname (raw_datum "np-place-overflow-and-trap")).

Definition wrong_mask : wexpr :=
  WIf (PLogNotTest (WLogor (TVar "V3015.12") (TVar "V3016.13")) (TImm 3))
    (WLet "t.19" (WAddOvfl (TVar "V3015.12") (TVar "V3016.13"))
       (WIf POverflow
          (WLabel "Lfail.20" (WPariah (WCallLib "+" [TVar "V3015.12"; TVar "V3016.13"])))
          (WTriv (TVar "t.19"))))
    (WGoto "Lfail.20").
Definition wrong_entry : wexpr :=
  WIf (PLogNotTest (WLogor (TVar "V3015.12") (TVar "V3016.13")) (TImm 7))
    (WLet "t.19" (WAddOvfl (TVar "V3015.12") (TVar "V3016.13"))
       (WIf POverflow
          (WLabel "Lfail.20" (WPariah (WCallLib "-" [TVar "V3015.12"; TVar "V3016.13"])))
          (WTriv (TVar "t.19"))))
    (WGoto "Lfail.20").
Definition wrong_order : wexpr :=
  WIf (PLogNotTest (WLogor (TVar "V3015.12") (TVar "V3016.13")) (TImm 7))
    (WLet "t.19" (WAddOvfl (TVar "V3015.12") (TVar "V3016.13"))
       (WIf POverflow
          (WLabel "Lfail.20" (WPariah (WCallLib "+" [TVar "V3016.13"; TVar "V3015.12"])))
          (WTriv (TVar "t.19"))))
    (WGoto "Lfail.20").

Theorem expand_rejects_wrong :
  expand_next = WGoto "" /\
  check_expand_plus expand_in expand_next = false /\
  check_expand_plus expand_in wrong_mask = false /\
  check_expand_plus expand_in wrong_entry = false /\
  check_expand_plus expand_in wrong_order = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- np-optimize-block-order! (L16 -> L16) ----------------------------- *)

Definition block_in : sexp := raw_or_nil (raw_datum "np-remove-repeater-blocks-again!").
Definition block_out : sexp := raw_or_nil (raw_datum "np-optimize-block-order!").

(* Ground derivations: the pass did reorder blocks (input and output
   differ), and the difference is block-list order only. *)
Theorem block_order_changed : sexp_eqb block_in block_out = false.
Proof. vm_compute. reflexivity. Qed.

Theorem block_order_checked : check_block_order block_in block_out = true.
Proof. vm_compute. reflexivity. Qed.

Theorem block_order_rejects :
  check_block_order (raw_or_nil (raw_datum "np-weight-references!")) block_out = false.
Proof. vm_compute. reflexivity. Qed.
