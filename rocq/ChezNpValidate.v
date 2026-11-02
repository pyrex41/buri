(* E2E-22 ground derivations on the captured compilation of
     (define (kl:buri-arm-add V3015 V3016) (+ V3015 V3016))
   by Chez Scheme 10.3.0 tarm64le (the shen-scheme v0.52 pin) under the
   parameters a running Shen-Scheme v0.52 reports.

   Every theorem here is about one captured artifact (ports/chez-np/
   tarm64le-buri-arm-add.np and ports/arm/chez/chez1030-buri-arm-add.hex and .relocs).
   They are ground derivations: a universally quantified checker soundness
   theorem (ChezNpCore, ChezNpReloc) applied to that data.  None of them is a
   theorem about Chez on other programs or other parameters. *)
From Coq Require Import String List Bool ZArith.
From Buri Require Import ChezNpReader ChezNpCore ChezNpReloc ChezNpCaptureInput.
Import ListNotations.
Open Scope string_scope.

Definition sections : list (string * string) := np_sections.

(* The first section printed under [name] (the register allocator's
   sub-passes print several times; none of them is used here). *)
Definition section_text (name : string) : option string :=
  option_map snd (find (fun p => String.eqb (fst p) name) sections).

Definition pass_datum (name : string) : option sexp :=
  match section_text name with Some t => read_exactly t | None => None end.

Definition datum_or_nil (o : option sexp) : sexp :=
  match o with Some x => x | None => Lst [] end.

Theorem trace_pass_order :
  map fst sections =
  ["cpnanopass"; "np-recognize-let"; "np-discover-names"; "np-convert-assignments";
   "np-sanitize-bindings"; "np-suppress-procedure-checks"; "np-recognize-mrvs";
   "np-expand-foreign"; "np-recognize-loops"; "np-recognize-attachment";
   "np-name-anonymous-lambda"; "np-convert-closures"; "np-optimize-direct-call";
   "np-identify-scc"; "np-lift-well-known-closures"; "np-expand/optimize-closures";
   "np-simplify-if"; "np-unbox-fp-vars!"; "$np-expand-primitives";
   "np-place-overflow-and-trap"; "np-rebind-on-ruined-path"; "np-finalize-loops";
   "np-optimize-pred-in-value"; "np-remove-complex-opera*"; "np-push-mrvs";
   "np-normalize-context"; "np-flatten-case-lambda"; "np-insert-trap-check";
   "np-impose-calling-conventions"; "np-expand-hand-coded";
   "np-expose-allocation-pointer"; "np-expose-basic-blocks";
   "np-remove-repeater-blocks!"; "np-propagate-pariahty!"; "np-add-in-links!";
   "np-compute-loop-depth!"; "np-weight-references!";
   "do-live-analysis!"; "record-call-live!"; "do-spillable-conflict!"; "assign-frame!";
   "record-inspector-information!"; "assign-new-frame!"; "record-fp-offsets!";
   "finalize-frame-locations!"; "select-instructions!"; "do-unspillable-conflict!";
   "assign-registers!"; "finalize-register-locations!"; "expose-overflow-check-blocks!";
   "do-live-analysis!"; "record-call-live!"; "do-spillable-conflict!"; "assign-frame!";
   "record-inspector-information!"; "assign-new-frame!"; "record-fp-offsets!";
   "finalize-frame-locations!"; "select-instructions!"; "do-unspillable-conflict!";
   "assign-registers!"; "finalize-register-locations!"; "expose-overflow-check-blocks!";
   "np-remove-repeater-blocks-again!"; "np-optimize-block-order!"; "np-generate-code"].
Proof. vm_compute. reflexivity. Qed.

(* ---- np-recognize-mrvs (L4 -> L4.5) ------------------------------------- *)

(* The input of np-recognize-mrvs is the output of the pass before it. *)
Definition mrvs_input : sexp := datum_or_nil (pass_datum "np-suppress-procedure-checks").
Definition mrvs_output : sexp := datum_or_nil (pass_datum "np-recognize-mrvs").

Theorem mrvs_input_read : pass_datum "np-suppress-procedure-checks" = Some mrvs_input.
Proof. vm_compute. reflexivity. Qed.

Theorem mrvs_output_read : pass_datum "np-recognize-mrvs" = Some mrvs_output.
Proof. vm_compute. reflexivity. Qed.

Theorem mrvs_buri_arm_add_checked : check_recognize_mrvs mrvs_input mrvs_output = true.
Proof. vm_compute. reflexivity. Qed.

Theorem mrvs_buri_arm_add_preserves :
  forall (World : Type) (prim : sexp -> list value -> World -> option (value * World))
    (order : nat -> list nat) (truthy : value -> bool) (fuel : nat) (w : World),
    sem false prim order truthy fuel mrvs_input w = sem true prim order truthy fuel mrvs_output w.
Proof.
  intros. apply (proj2 (check_recognize_mrvs_sound _ _ mrvs_buri_arm_add_checked)).
Qed.

(* The validator is not vacuous on this artifact: it rejects the pass's
   input paired with a later pass's output (np-name-anonymous-lambda adds a
   letrec it cannot relate) and the pair swapped. *)
Theorem mrvs_rejects_wrong_pairs :
  check_recognize_mrvs mrvs_input (datum_or_nil (pass_datum "np-name-anonymous-lambda")) = false /\
  check_recognize_mrvs mrvs_output mrvs_input = false.
Proof. vm_compute. split; reflexivity. Qed.

(* ---- printed identity of same-language passes --------------------------- *)

(* (input pass, pass, language).  For each pair the pass's printed output
   equals its printed input.  The unparser omits info fields (e.g. the
   application flags np-suppress-procedure-checks exists to change), so this
   is identity of the printed form only. *)
Definition identity_passes : list (string * string * string) :=
  [("np-convert-assignments", "np-sanitize-bindings", "L4");
   ("np-sanitize-bindings", "np-suppress-procedure-checks", "L4");
   ("np-convert-closures", "np-optimize-direct-call", "L6");
   ("np-optimize-direct-call", "np-identify-scc", "L6");
   ("np-identify-scc", "np-lift-well-known-closures", "L6");
   ("np-expand/optimize-closures", "np-simplify-if", "L7");
   ("np-simplify-if", "np-unbox-fp-vars!", "L7");
   ("np-place-overflow-and-trap", "np-rebind-on-ruined-path", "L9.5");
   ("np-finalize-loops", "np-optimize-pred-in-value", "L9.75");
   ("np-add-in-links!", "np-compute-loop-depth!", "L15a")].

Definition identity_holds (p : string * string * string) : bool :=
  let '(a, b, _) := p in
  match pass_datum a, pass_datum b with
  | Some x, Some y => check_printed_identity x y
  | _, _ => false
  end.

Theorem identity_passes_checked : forallb identity_holds identity_passes = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- np-generate-code -> exact tarm64le bytes ---------------------------- *)

(* Helper functions keep the closed scrutinees out of [match] at definition
   time: Coq's match elaboration would otherwise evaluate them eagerly. *)
Definition code_record_of (o : option sexp) : option (Z * list sexp) :=
  match o with Some x => find_code 64 "kl:buri-arm-add" x | None => None end.
Definition size_of (o : option (Z * list sexp)) : Z :=
  match o with Some (s, _) => s | None => 0%Z end.
Definition layout_of (o : option (Z * list sexp)) : list Z * list reloc :=
  match o with
  | Some (_, es) => match layout 0 es with Some r => r | None => ([], []) end
  | None => ([], [])
  end.
Definition bytes_or_nil (o : option (list Z)) : list Z :=
  match o with Some b => b | None => [] end.
Definition table_or_nil (o : option (list (string * nat))) : list (string * nat) :=
  match o with Some t => t | None => [] end.

Definition code_record : option (Z * list sexp) := code_record_of (pass_datum "np-generate-code").
Definition code_size : Z := size_of code_record.
Definition code_layout : list Z * list reloc := layout_of code_record.
Definition code_template : list Z := fst code_layout.
Definition code_relocs : list reloc := snd code_layout.
Definition captured_bytes : list Z := bytes_or_nil (bytes_of_hex arm_code_hex).
Definition captured_table : list (string * nat) :=
  table_or_nil (relocs_of_lines (split_lines arm_code_relocs)).

Theorem code_shape :
  code_size = 152%Z /\
  length captured_bytes = 152 /\
  map r_offset code_relocs = [64; 112; 132] /\
  captured_table = [("#<code doargerr>", 132); ("#<code +>", 112); ("#<code event>", 64)].
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem codegen_buri_arm_add_checked :
  check_code_object code_template code_relocs code_size captured_bytes captured_table = true.
Proof. vm_compute. reflexivity. Qed.

(* The 152 captured bytes are exactly np-generate-code's template for
   kl:buri-arm-add with its three library-entry windows (event, +,
   doargerr) instantiated by arm64_set_abs. *)
Theorem codegen_buri_arm_add_instance :
  captured_bytes = instantiate code_template code_relocs (items_of captured_bytes code_relocs).
Proof. exact (proj1 (check_code_object_sound _ _ _ _ _ codegen_buri_arm_add_checked)). Qed.

(* Tampering with one non-relocated byte, or with a relocation window's
   destination register, is rejected. *)
Definition flip (bs : list Z) (i : nat) : list Z := overwrite bs i [Z.lxor (nth i bs 0%Z) 1].

Theorem codegen_rejects_tampering :
  check_code_object code_template code_relocs code_size (flip captured_bytes 0) captured_table = false /\
  check_code_object code_template code_relocs code_size (flip captured_bytes 76) captured_table = false /\
  check_code_object code_template code_relocs code_size captured_bytes (tl captured_table) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
